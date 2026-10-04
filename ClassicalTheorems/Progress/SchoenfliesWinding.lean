/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.SchoenfliesBridge
import Mathlib.Data.Int.Order.Units

/-! Primitive winding for every simple closed planar loop, using Schönflies. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- An ambient circle chart constructs a point about which a simple loop winds once. -/
theorem winding_witness_of_ambient_circle (x : Icc (0 : ℝ) 1 → Point)
    (hx : Continuous x) (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1})
    (e : Point ≃ₜ Point) (he : e '' Metric.sphere (0 : Point) 1 = range x) :
    ∃ p : Point, |curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p| = 1 := by
  let p := e 0
  let y : Icc (0 : ℝ) 1 → Point := fun t => e.symm (x t)
  have hymem (t : Icc (0 : ℝ) 1) : y t ∈ Metric.sphere (0 : Point) 1 := by
    obtain ⟨w, hw, hew⟩ := he.symm.subset (mem_range_self t)
    have h : e.symm (x t) = w := by rw [← hew, e.symm_apply_apply]
    change e.symm (x t) ∈ Metric.sphere (0 : Point) 1
    rw [h]
    exact hw
  have hp : p ∉ range x := by
    rintro ⟨t, ht⟩
    have h := hymem t
    simp [y, ht, p] at h
  have hyc : Continuous y := e.symm.continuous.comp hx
  have hyclosed : y ⟨0, by norm_num⟩ = y ⟨1, by norm_num⟩ := congrArg e.symm hclosed
  have hyinj : InjOn y {t | (t : ℝ) < 1} := by
    intro s hs t ht hst
    exact hinj hs ht (e.symm.injective hst)
  have hyw := circle_winding_center_abs_one_of_mem y 0 1 (by norm_num)
    hyc hymem hyclosed hyinj
  obtain ⟨D⟩ := nonempty_integer_circle_deformation (by norm_num : (0 : ℝ) < 1)
    x p hx hp hclosed
  let H : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 → Point := fun u t => e.symm (D.H u t)
  have hH : Continuous (Function.uncurry H) := e.symm.continuous.comp D.continuous
  have hHclosed (u : Icc (0 : ℝ) 1) : H u ⟨0, by norm_num⟩ = H u ⟨1, by norm_num⟩ :=
    congrArg e.symm (D.closed u)
  have hHavoid (u : Icc (0 : ℝ) 1) : (0 : Point) ∉ range (H u) := by
    rintro ⟨t, ht⟩
    have h : D.H u t = p := by
      have h' := congrArg e ht
      simpa [H, p] using h'
    exact D.avoids u ⟨t, h⟩
  have hwH := winding_eq_of_continuous_deformation (by norm_num : (0 : ℝ) < 1)
    H 0 hH hHclosed hHavoid
  let f : ℝ → Point := fun t => e.symm (p + angularPoint (D.phase + 2 * Real.pi * t))
  have hf : Continuous f := e.symm.continuous.comp
    (continuous_const.add (continuous_angularPoint.comp (by fun_prop)))
  have hfavoid : (0 : Point) ∉ range f := by
    rintro ⟨t, ht⟩
    have h : p + angularPoint (D.phase + 2 * Real.pi * t) = p := by
      have h' := congrArg e ht
      simpa [f, p] using h'
    have hzero : angularPoint (D.phase + 2 * Real.pi * t) = 0 :=
      add_left_cancel (h.trans (add_zero p).symm)
    have hn := norm_angularPoint (D.phase + 2 * Real.pi * t)
    rw [hzero, norm_zero] at hn
    exact zero_ne_one hn
  have hfperiod : Function.Periodic f 1 := by
    intro t
    dsimp [f]
    congr 2
    rw [show D.phase + 2 * Real.pi * (t + 1) =
      (D.phase + 2 * Real.pi * t) + 2 * Real.pi by ring]
    simp [angularPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
  obtain ⟨m, -, hwm⟩ := winding_periodic_integer_traversal
    (by norm_num : (0 : ℝ) < 1) f 0 hf hfavoid hfperiod 0 D.degree
  have hstart : H ⟨0, by norm_num⟩ = y := by
    funext t
    change e.symm (D.H ⟨0, by norm_num⟩ t) = e.symm (x t)
    rw [D.start]
  have hfinish : H ⟨1, by norm_num⟩ =
      (fun t : Icc (0 : ℝ) 1 => f (0 + (D.degree : ℝ) * (((t : ℝ) - 0) / (1 - 0)))) := by
    funext t
    simp only [H, D.finish, f, sub_zero, div_one, zero_add]
    congr 2
    ring
  rw [hstart, hfinish, hwm] at hwH
  have hmul : |(D.degree : ℝ) * (m : ℝ)| = 1 := hwH ▸ hyw
  have hmulInt : |D.degree * m| = (1 : ℤ) := by exact_mod_cast hmul
  have hnInt : |D.degree| = (1 : ℤ) :=
    Int.isUnit_iff_abs_eq.mp (isUnit_of_mul_isUnit_left (Int.isUnit_iff_abs_eq.mpr hmulInt))
  refine ⟨p, ?_⟩
  rw [D.winding_eq]
  exact_mod_cast hnInt

/-- Every simple closed unit-interval loop supplies its own interior winding witness. -/
theorem simple_jordan_winding_witness_unit (x : Icc (0 : ℝ) 1 → Point)
    (hx : Continuous x) (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) :
    ∃ p ∈ jordanInterior (range x),
      |curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p| = 1 := by
  obtain ⟨e, he⟩ := exists_circle_ambient_homeomorph x hx hclosed hinj
  obtain ⟨p, hp⟩ := winding_witness_of_ambient_circle x hx hclosed hinj e he
  refine ⟨p, mem_jordanInterior_of_winding_ne_zero (by norm_num) x (range x)
    hx rfl hclosed p ?_, hp⟩
  intro h
  simp [h] at hp

/-- A simple closed Jordan parametrization determines its own global orientation. -/
theorem simple_jordan_is_oriented {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x := by
  obtain ⟨φ, hc, _, hs, hf⟩ :=
    Icc.exists_affine_monotone_surjection (by norm_num : (0 : ℝ) < 1) hab
  have hv (t : Icc (0 : ℝ) 1) : (φ t : ℝ) = a + (t : ℝ) * (b - a) := by
    simpa using hf t
  have hφa : φ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab.le⟩ := by
    apply Subtype.ext
    simp [hv]
  have hφb : φ ⟨1, by norm_num⟩ = ⟨b, hab.le, le_rfl⟩ := by
    apply Subtype.ext
    simp [hv]
  have hφinj : Function.Injective φ := by
    intro s t he
    have h := congrArg Subtype.val he
    rw [hv, hv] at h
    apply Subtype.ext
    nlinarith [hab]
  have hclosed' : (x ∘ φ) ⟨0, by norm_num⟩ = (x ∘ φ) ⟨1, by norm_num⟩ := by
    simpa only [Function.comp_def, hφa, hφb] using hclosed
  have hinj' : InjOn (x ∘ φ) {t | (t : ℝ) < 1} := by
    intro s hss t htt hst
    apply hφinj
    apply hinj _ _ hst
    · change (φ s : ℝ) < b
      rw [hv]
      have hh : (s : ℝ) < 1 := hss
      nlinarith [hab]
    · change (φ t : ℝ) < b
      rw [hv]
      have hh : (t : ℝ) < 1 := htt
      nlinarith [hab]
  obtain ⟨p, hp, hw⟩ := simple_jordan_winding_witness_unit (x ∘ φ)
    (hx.comp hc) hclosed' hinj'
  have hr : range (x ∘ φ) = Γ := by
    rw [Function.Surjective.range_comp hs, hrange]
  rw [hr] at hp
  have hpavoid : p ∉ range x := hrange ▸ hp.1
  rw [curveWinding_comp_of_endpoints hab.le (by norm_num)
    (exists_curveAngleLift_of_avoids hab hx hpavoid) hc hφa hφb] at hw
  exact oriented_jordan_of_winding_witness hab x Γ hΓ hx hrange hclosed hinj p hp hw

/-- Every interior point of a simple Jordan loop has winding of absolute value one. -/
theorem simple_jordan_winding_abs_one {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) (p : Point) (hp : p ∈ jordanInterior Γ) :
    |curveWinding hab.le x p| = 1 := by
  obtain ⟨orientation, ho⟩ := simple_jordan_is_oriented hab x Γ hΓ hx hrange hclosed hinj
  rw [ho.2.2.2.2.2.2 p hp]
  cases orientation <;> norm_num

/-- Sharp rectifiable Jordan isoperimetry, including circle equality, with no winding input. -/
theorem jordan_isoperimetric_unconditional (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Γ) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht hst
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ hst)
  obtain ⟨orientation, ho⟩ := simple_jordan_is_oriented hab
    (fun t : Icc a b => γ t) Γ hΓ hc.domRestrict hr hclosed hi
  exact jordan_isoperimetric_rectifiable_interval γ hab hBV Γ orientation ho

end ClassicalTheorems.Progress.Isoperimetric

#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_witness_of_ambient_circle
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_jordan_winding_witness_unit
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_jordan_is_oriented
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_unconditional

#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_jordan_winding_abs_one

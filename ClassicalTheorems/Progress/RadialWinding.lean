/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.CircleWinding
import Mathlib.Analysis.Convex.Topology

/-! Automatic orientation from radial geometry, including convex Jordan interiors. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The unit direction from a basepoint to a boundary point. -/
def radialDirection (p z : Point) : Point := ‖z - p‖⁻¹ • (z - p)

/-- A simple closed path with injective radial projection winds exactly once
about its basepoint. This is a geometric condition, not a winding assumption. -/
theorem winding_abs_one_of_radial_inj_unit (x : Icc (0 : ℝ) 1 → Point)
    (p : Point) (hc : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1})
    (hrad : InjOn (radialDirection p) (range x)) :
    |curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p| = 1 := by
  let y : Icc (0 : ℝ) 1 → Point := fun t => radialDirection p (x t)
  have hn (t : Icc (0 : ℝ) 1) : ‖x t - p‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    exact sub_ne_zero.mpr (fun he => hp ⟨t, he⟩)
  have hyc : Continuous y :=
    ((hc.sub continuous_const).norm.inv₀ hn).smul (hc.sub continuous_const)
  have hyn (t : Icc (0 : ℝ) 1) : ‖y t‖ = 1 := by
    simp [y, radialDirection, norm_smul, hn t]
  have hyclosed : y ⟨0, by norm_num⟩ = y ⟨1, by norm_num⟩ := by
    simp only [y, hclosed]
  have hyinj : InjOn y {t | (t : ℝ) < 1} := by
    intro s hs t ht he
    exact hinj hs ht (hrad (mem_range_self s) (mem_range_self t) he)
  have hw := circle_winding_center_abs_one_of_mem y 0 1 (by norm_num) hyc
    (fun t => mem_sphere_zero_iff_norm.mpr (hyn t)) hyclosed hyinj
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids
    (by norm_num : (0 : ℝ) < 1) hc hp
  have hyθ : IsCurveAngleLift y 0 θ := by
    refine ⟨hθ.1, fun t => ?_⟩
    rw [sub_zero, hyn, div_one, div_one]
    constructor
    · rw [(hθ.2 t).1]
      simp [y, radialDirection, PiLp.smul_apply, div_eq_mul_inv, mul_comm]
    · rw [(hθ.2 t).2]
      simp [y, radialDirection, PiLp.smul_apply, div_eq_mul_inv, mul_comm]
  have hwEq : curveWinding (by norm_num : (0 : ℝ) ≤ 1) y 0 =
      curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p := by
    rw [hyθ.curveWinding_eq, hθ.curveWinding_eq]
  simpa only [hwEq] using hw

/-- Radial uniqueness gives one full turn on every nondegenerate parameter interval. -/
theorem winding_abs_one_of_radial_inj {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) (hc : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b})
    (hrad : InjOn (radialDirection p) (range x)) :
    |curveWinding hab.le x p| = 1 := by
  obtain ⟨φ, hφc, _, hφs, hf⟩ :=
    Icc.exists_affine_monotone_surjection (by norm_num : (0 : ℝ) < 1) hab
  have hv (t : Icc (0 : ℝ) 1) : (φ t : ℝ) = a + (t : ℝ) * (b - a) := by
    simpa using hf t
  have hφa : φ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab.le⟩ := by
    apply Subtype.ext
    simp [hv]
  have hφb : φ ⟨1, by norm_num⟩ = ⟨b, hab.le, le_rfl⟩ := by
    apply Subtype.ext
    simp [hv]
  have hφi : Function.Injective φ := by
    intro s t he
    have he' := congrArg Subtype.val he
    rw [hv, hv] at he'
    apply Subtype.ext
    nlinarith [hab]
  have hr : range (x ∘ φ) = range x := Function.Surjective.range_comp hφs x
  have hi : InjOn (x ∘ φ) {t | (t : ℝ) < 1} := by
    intro s hs t ht he
    apply hφi
    apply hinj _ _ he
    · change (φ s : ℝ) < b
      rw [hv]
      have hs' : (s : ℝ) < 1 := hs
      nlinarith [hab]
    · change (φ t : ℝ) < b
      rw [hv]
      have ht' : (t : ℝ) < 1 := ht
      nlinarith [hab]
  have hcl : (x ∘ φ) ⟨0, by norm_num⟩ = (x ∘ φ) ⟨1, by norm_num⟩ := by
    simpa only [Function.comp_def, hφa, hφb] using hclosed
  have hw := winding_abs_one_of_radial_inj_unit (x ∘ φ) p (hc.comp hφc)
    (hr ▸ hp) hcl hi (hr ▸ hrad)
  rw [curveWinding_comp_of_endpoints hab.le (by norm_num : (0 : ℝ) ≤ 1)
    (exists_curveAngleLift_of_avoids hab hc hp) hφc hφa hφb] at hw
  exact hw

/-- An interior point of a convex set sees at most one frontier point on each ray. -/
theorem convex_frontier_radial_inj (K : Set Point) (hK : Convex ℝ K)
    (p : Point) (hp : p ∈ interior K) : InjOn (radialDirection p) (frontier K) := by
  have hneq {z : Point} (hz : z ∈ frontier K) : z - p ≠ 0 := by
    intro he
    have he' : z = p := sub_eq_zero.mp he
    subst z
    exact disjoint_interior_frontier.le_bot ⟨hp, hz⟩
  have hnorm {z : Point} (hz : z ∈ frontier K) : 0 < ‖z - p‖ :=
    norm_pos_iff.mpr (hneq hz)
  have impossible {x y : Point} (hx : x ∈ frontier K) (hy : y ∈ frontier K)
      (he : radialDirection p x = radialDirection p y) (hlt : ‖x - p‖ < ‖y - p‖) : False := by
    let t := ‖x - p‖ / ‖y - p‖
    have ht0 : 0 ≤ t := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have ht1 : t < 1 := (div_lt_one (hnorm hy)).mpr hlt
    have hxform : x - p = t • (y - p) := by
      have h := congrArg (fun v : Point => ‖x - p‖ • v) he
      simpa only [radialDirection, smul_smul, mul_inv_cancel₀ (hnorm hx).ne',
        one_smul, ← div_eq_mul_inv] using h
    have heq : (1 - t) • p + t • y = x := by
      calc
        _ = p + t • (y - p) := by module
        _ = p + (x - p) := by rw [hxform]
        _ = x := by abel
    have hxint := hK.combo_interior_closure_mem_interior hp
      (frontier_subset_closure hy) (sub_pos.mpr ht1) ht0 (by ring : 1 - t + t = 1)
    rw [heq] at hxint
    exact disjoint_interior_frontier.le_bot ⟨hxint, hx⟩
  intro x hx y hy he
  have hn : ‖x - p‖ = ‖y - p‖ := by
    rcases lt_trichotomy ‖x - p‖ ‖y - p‖ with h | h | h
    · exact False.elim (impossible hx hy he h)
    · exact h
    · exact False.elim (impossible hy hx he.symm h)
  have h := congrArg (fun v : Point => ‖x - p‖ • v) he
  simp only [radialDirection, ← hn, smul_smul, mul_inv_cancel₀ (hnorm hx).ne', one_smul] at h
  exact (sub_left_inj).mp h

/-- A Jordan interior is open; separation identifies it with the bounded open component. -/
theorem jordanInterior_isOpen {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    IsOpen (jordanInterior Γ) := by
  obtain ⟨p, hp⟩ := hΓ.jordanInterior_nonempty
  obtain ⟨U, V, hU, _, _, _, _, hVb, _, hcover, _, _, hUc, hVc⟩ := jordan_separation hΓ
  have hpU : p ∈ U := by
    rcases hcover.symm.subset hp.1 with h | h
    · exact h
    · exact False.elim (hVb (hVc p h ▸ hp.2))
  rw [jordanInterior_eq_component hΓ hp, hUc p hpU]
  exact hU

/-- Every interior point of a convex Jordan interior supplies automatic orientation. -/
theorem convex_jordan_is_oriented {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hconvex : Convex ℝ (jordanInterior Γ)) (hc : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x := by
  obtain ⟨p, hp⟩ := hΓ.jordanInterior_nonempty
  have hpint : p ∈ interior (jordanInterior Γ) := by
    simpa only [(jordanInterior_isOpen hΓ).interior_eq] using hp
  have hrad : InjOn (radialDirection p) (range x) := by
    rw [hrange, ← hΓ.frontier_jordanInterior]
    exact convex_frontier_radial_inj _ hconvex p hpint
  have havoid : p ∉ range x := hrange ▸ hp.1
  have hw := winding_abs_one_of_radial_inj hab x p hc havoid hclosed hinj hrad
  exact oriented_jordan_of_winding_witness hab x Γ hΓ hc hrange hclosed hinj p hp hw

/-- The full rectifiable isoperimetric theorem for convex Jordan interiors,
with no winding or orientation hypothesis. -/
theorem jordan_isoperimetric_convex (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hconvex : Convex ℝ (jordanInterior Γ))
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hrange' : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨orientation, ho⟩ := convex_jordan_is_oriented hab
    (fun t : Icc a b => γ t) Γ hΓ hconvex hc.domRestrict hrange' hclosed hi
  exact jordan_isoperimetric_rectifiable_interval γ hab hBV Γ orientation ho

/-- A boundary with one point per radial direction satisfies the full sharp
theorem using only geometric input, without a winding check. -/
theorem jordan_isoperimetric_radial (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (p : Point) (hp : p ∈ jordanInterior Γ)
    (hrad : InjOn (radialDirection p) Γ) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  have hw := winding_abs_one_of_radial_inj hab (fun t : Icc a b => γ t) p
    hc.domRestrict (hr ▸ hp.1) hclosed hi (hr ▸ hrad)
  exact jordan_isoperimetric_of_winding_witness γ hab hBV Γ hΓ hc hrange hclosed hinj p hp hw

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.radialDirection
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_abs_one_of_radial_inj_unit
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_abs_one_of_radial_inj
#check_upstream ClassicalTheorems.Progress.Isoperimetric.convex_frontier_radial_inj
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordanInterior_isOpen
#check_upstream ClassicalTheorems.Progress.Isoperimetric.convex_jordan_is_oriented
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_convex
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_radial

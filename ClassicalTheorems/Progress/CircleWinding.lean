/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.JordanWindingWitness

/-! A simple closed circular parametrization determines its own orientation. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A continuous real lift of a path injective before its terminal endpoint
cannot have equal endpoint values. -/
theorem simple_real_lift_endpoints_ne (x : Icc (0 : ℝ) 1 → Point)
    (θ : Icc (0 : ℝ) 1 → ℝ) (hc : Continuous θ)
    (hinj : InjOn x {t | (t : ℝ) < 1})
    (hlift : ∀ s t, θ s = θ t → x s = x t) :
    θ ⟨0, by norm_num⟩ ≠ θ ⟨1, by norm_num⟩ := by
  let A : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let M : Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
  let B : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have ham : A < M := by change (0 : ℝ) < 1 / 2; norm_num
  have hmb : M < B := by change (1 / 2 : ℝ) < 1; norm_num
  have hm : θ M ≠ θ A := by
    intro h
    have he := hinj (x₁ := M) (x₂ := A) (by change (1 / 2 : ℝ) < 1; norm_num)
      (by norm_num [A]) (hlift M A h)
    exact ham.ne he.symm
  intro hend
  change θ A = θ B at hend
  let z := (θ A + θ M) / 2
  have collide (u v : Icc (0 : ℝ) 1) (hu : u ∈ Ioo A M) (hv : v ∈ Ioo M B)
      (he : θ u = θ v) : False := by
    have hu1 : (u : ℝ) < 1 := lt_trans hu.2 (by norm_num [M])
    have hv1 : (v : ℝ) < 1 := hv.2
    exact (hu.2.trans hv.1).ne (hinj hu1 hv1 (hlift u v he))
  rcases lt_or_gt_of_ne hm with hm | hm
  · obtain ⟨u, hu, heu⟩ := intermediate_value_Ioo' ham.le hc.continuousOn
      (show z ∈ Ioo (θ M) (θ A) by dsimp [z]; constructor <;> linarith)
    obtain ⟨v, hv, hev⟩ := intermediate_value_Ioo hmb.le hc.continuousOn
      (show z ∈ Ioo (θ M) (θ B) by dsimp [z]; constructor <;> linarith)
    exact collide u v hu hv (heu.trans hev.symm)
  · obtain ⟨u, hu, heu⟩ := intermediate_value_Ioo ham.le hc.continuousOn
      (show z ∈ Ioo (θ A) (θ M) by dsimp [z]; constructor <;> linarith)
    obtain ⟨v, hv, hev⟩ := intermediate_value_Ioo' hmb.le hc.continuousOn
      (show z ∈ Ioo (θ B) (θ M) by dsimp [z]; constructor <;> linarith)
    exact collide u v hu hv (heu.trans hev.symm)

/-- Simplicity alone fixes the absolute angular increment of a circular path
to one full turn. No winding or orientation assumption is imposed. -/
theorem circle_winding_center_abs_one_of_mem (x : Icc (0 : ℝ) 1 → Point)
    (c : Point) (r : ℝ) (hr : 0 < r) (hc : Continuous x)
    (hmem : ∀ t, x t ∈ Metric.sphere c r)
    (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) :
    |curveWinding (by norm_num : (0 : ℝ) ≤ 1) x c| = 1 := by
  have havoid : c ∉ range x := by
    rintro ⟨t, ht⟩
    have h := hmem t
    rw [ht] at h
    exact hr.ne (by simpa using h)
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids
    (by norm_num : (0 : ℝ) < 1) hc havoid
  let A : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  let B : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  have hrepr (t : Icc (0 : ℝ) 1) : x t = c + r •
      Complex.orthonormalBasisOneI.repr (Real.cos (θ t) + Real.sin (θ t) * Complex.I) := by
    have ht : x t ∈ Metric.sphere c r := hmem t
    have hn : ‖x t - c‖ = r := mem_sphere_iff_norm.mp ht
    have he0 := (hθ.2 t).1
    have he1 := (hθ.2 t).2
    rw [hn] at he0 he1
    have hd0 := (eq_div_iff hr.ne').mp he0
    have hd1 := (eq_div_iff hr.ne').mp he1
    ext i
    fin_cases i <;>
      simp [Complex.orthonormalBasisOneI_repr_apply, Complex.mul_re, Complex.mul_im]
    · change x t 0 = c 0 + r * Real.cos (θ t)
      change Real.cos (θ t) * r = x t 0 - c 0 at hd0
      nlinarith
    · change x t 1 = c 1 + r * Real.sin (θ t)
      change Real.sin (θ t) * r = x t 1 - c 1 at hd1
      nlinarith
  have hlift (s t : Icc (0 : ℝ) 1) (he : θ s = θ t) : x s = x t := by
    rw [hrepr s, hrepr t, he]
  have hne : θ A ≠ θ B := simple_real_lift_endpoints_ne x θ hθ.1 hinj hlift
  have htrig : Real.cos (θ B - θ A) = 1 := by
    have hcos : Real.cos (θ B) = Real.cos (θ A) := by
      rw [(hθ.2 B).1, (hθ.2 A).1]
      simp only [A, B, hclosed]
    have hsin : Real.sin (θ B) = Real.sin (θ A) := by
      rw [(hθ.2 B).2, (hθ.2 A).2]
      simp only [A, B, hclosed]
    rw [Real.cos_sub, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (θ A)]
  have hperiod (t : Icc (0 : ℝ) 1) (h : θ t = θ A + 2 * Real.pi ∨
      θ t = θ A - 2 * Real.pi) : x t = x A := by
    rcases h with h | h
    · rw [hrepr t, hrepr A, h]
      simp
    · rw [hrepr t, hrepr A, h]
      simp
  have hupper : θ B - θ A ≤ 2 * Real.pi := by
    by_contra! h
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo (show A ≤ B by norm_num [A, B])
      hθ.1.continuousOn
      (show θ A + 2 * Real.pi ∈ Ioo (θ A) (θ B) by
        constructor <;> linarith [Real.pi_pos])
    have ht1 : (t : ℝ) < 1 := ht.2
    have heq := hinj (x₁ := t) (x₂ := A) ht1 (by norm_num [A])
      (hperiod t (Or.inl he))
    exact ht.1.ne heq.symm
  have hlower : -(2 * Real.pi) ≤ θ B - θ A := by
    by_contra! h
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo' (show A ≤ B by norm_num [A, B])
      hθ.1.continuousOn
      (show θ A - 2 * Real.pi ∈ Ioo (θ B) (θ A) by
        constructor <;> linarith [Real.pi_pos])
    have ht1 : (t : ℝ) < 1 := ht.2
    have heq := hinj (x₁ := t) (x₂ := A) ht1 (by norm_num [A])
      (hperiod t (Or.inr he))
    exact ht.1.ne heq.symm
  have hboundary : θ B - θ A = 2 * Real.pi ∨ θ B - θ A = -(2 * Real.pi) := by
    by_contra! h
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt
      (lt_of_le_of_ne hlower h.2.symm) (lt_of_le_of_ne hupper h.1)).mp htrig
    exact hne (sub_eq_zero.mp hzero).symm
  rw [hθ.curveWinding_eq (by norm_num)]
  change |(θ B - θ A) / (2 * Real.pi)| = 1
  rcases hboundary with h | h <;> rw [h] <;> field_simp <;> simp

/-- The range-equality interface for circular winding, using equality of curve ranges. -/
theorem circle_winding_center_abs_one (x : Icc (0 : ℝ) 1 → Point)
    (c : Point) (r : ℝ) (hr : 0 < r) (hc : Continuous x)
    (hrange : range x = Metric.sphere c r)
    (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) :
    |curveWinding (by norm_num : (0 : ℝ) ≤ 1) x c| = 1 :=
  circle_winding_center_abs_one_of_mem x c r hr hc
    (fun t => hrange ▸ mem_range_self t) hclosed hinj

/-- A positive-radius Euclidean circle is a Jordan curve. -/
theorem sphere_isJordanCurve (c : Point) (r : ℝ) (hr : 0 < r) :
    IsJordanCurve (Metric.sphere c r) := by
  let T : ℂ ≃ₗᵢ[ℝ] Point := Complex.orthonormalBasisOneI.repr
  let f : Circle → Point := fun z => c + r • T (z : ℂ)
  refine ⟨f, continuous_const.add
    ((T.continuous.comp continuous_subtype_val).const_smul r), ?_, ?_⟩
  · intro z w h
    apply Subtype.ext
    apply T.injective
    have hs : r • T (z : ℂ) = r • T (w : ℂ) := add_left_cancel h
    exact (smul_right_injective Point hr.ne') hs
  · ext p
    constructor
    · rintro ⟨z, rfl⟩
      apply mem_sphere_iff_norm.mpr
      simp [f, norm_smul, T.norm_map, abs_of_pos hr]
    · intro hp
      have hn : ‖p - c‖ = r := mem_sphere_iff_norm.mp hp
      let z : Circle := ⟨T.symm (r⁻¹ • (p - c)), mem_sphere_zero_iff_norm.mpr (by
        rw [T.symm.norm_map, norm_smul, hn, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
        exact inv_mul_cancel₀ hr.ne')⟩
      refine ⟨z, ?_⟩
      change c + r • T (T.symm (r⁻¹ • (p - c))) = p
      rw [T.apply_symm_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel

/-- The bounded-component interior of a circle is exactly its open disk. -/
theorem jordanInterior_sphere_eq_ball (c : Point) (r : ℝ) (hr : 0 < r) :
    jordanInterior (Metric.sphere c r) = Metric.ball c r := by
  apply Subset.antisymm _ (ball_subset_jordanInterior_sphere c r)
  have hc : c ∈ jordanInterior (Metric.sphere c r) :=
    ball_subset_jordanInterior_sphere c r (Metric.mem_ball_self hr)
  have hconn : IsPreconnected (jordanInterior (Metric.sphere c r)) := by
    rw [jordanInterior_eq_component (sphere_isJordanCurve c r hr) hc]
    exact isPreconnected_connectedComponentIn
  intro p hp
  by_contra h
  have hpr : r ≤ dist p c := le_of_not_gt (fun hlt => h (Metric.mem_ball.mpr hlt))
  obtain ⟨q, hq, he⟩ := hconn.intermediate_value hc hp
    (continuous_id.dist continuous_const).continuousOn
    (show r ∈ Icc (dist c c) (dist p c) by simpa using ⟨hr.le, hpr⟩)
  exact hq.1 (Metric.mem_sphere.mpr he)

/-- Circle orientation follows from continuity, closedness and simplicity alone. -/
theorem simple_circle_is_oriented {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (c : Point) (r : ℝ) (hr : 0 < r)
    (hc : Continuous x) (hrange : range x = Metric.sphere c r)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) :
    ∃ orientation : Bool,
      IsOrientedJordanParametrization hab.le (Metric.sphere c r) orientation x := by
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
    have hvv := congrArg Subtype.val he
    rw [hv, hv] at hvv
    apply Subtype.ext
    nlinarith [hab]
  have hri : range (x ∘ φ) = Metric.sphere c r := by
    rw [Function.Surjective.range_comp hφs, hrange]
  have hcl : (x ∘ φ) ⟨0, by norm_num⟩ = (x ∘ φ) ⟨1, by norm_num⟩ := by
    simpa only [Function.comp_def, hφa, hφb] using hclosed
  have hi : InjOn (x ∘ φ) {t | (t : ℝ) < 1} := by
    intro s hs t ht he
    apply hφi
    apply hinj _ _ he
    · change (φ s : ℝ) < b
      rw [hv]
      have hss : (s : ℝ) < 1 := hs
      nlinarith [hab]
    · change (φ t : ℝ) < b
      rw [hv]
      have htt : (t : ℝ) < 1 := ht
      nlinarith [hab]
  have hw := circle_winding_center_abs_one (x ∘ φ) c r hr (hc.comp hφc) hri hcl hi
  have hcint : c ∈ jordanInterior (Metric.sphere c r) :=
    ball_subset_jordanInterior_sphere c r (Metric.mem_ball_self hr)
  have havoid : c ∉ range x := by
    rw [hrange]
    simpa using hr.ne
  rw [curveWinding_comp_of_endpoints hab.le (by norm_num : (0 : ℝ) ≤ 1)
    (exists_curveAngleLift_of_avoids hab hc havoid) hφc hφa hφb] at hw
  exact oriented_jordan_of_winding_witness hab x (Metric.sphere c r)
    (sphere_isJordanCurve c r hr) hc hrange hclosed hinj c hcint hw

/-- The geometric area of the Jordan interior of a circle, without a parametrization. -/
theorem circle_geometric_area (c : Point) (r : ℝ) (hr : 0 < r) :
    (volume (jordanInterior (Metric.sphere c r))).toReal = Real.pi * r ^ 2 := by
  rw [jordanInterior_sphere_eq_ball c r hr, EuclideanSpace.volume_ball_fin_two]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_nonneg, mul_comm]

/-- Exact area and circumference of a simple rectifiable circle parametrization
on any compact interval, with no winding or orientation input. -/
theorem simple_circle_area_perimeter (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (c : Point) (r : ℝ) (hr : 0 < r) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Metric.sphere c r) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) :
    (volume (jordanInterior (Metric.sphere c r))).toReal = Real.pi * r ^ 2 ∧
      (eVariationOn γ (Icc a b)).toReal = 2 * Real.pi * r := by
  have hrange' : range (fun t : Icc a b => γ t) = Metric.sphere c r := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨orientation, ho⟩ := simple_circle_is_oriented hab
    (fun t : Icc a b => γ t) c r hr hc.domRestrict hrange' hclosed hi
  exact circle_area_perimeter_interval γ hab hBV (Metric.sphere c r) orientation
    ho c r hr rfl

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_real_lift_endpoints_ne
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_winding_center_abs_one_of_mem
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_winding_center_abs_one
#check_upstream ClassicalTheorems.Progress.Isoperimetric.sphere_isJordanCurve
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordanInterior_sphere_eq_ball
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_circle_is_oriented
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_geometric_area
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_circle_area_perimeter

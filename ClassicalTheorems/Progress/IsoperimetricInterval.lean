/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricCircleIff

/-! Parameter-independent sharp isoperimetry and exact circular area/perimeter. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A simple rectifiable circular boundary has the usual area and circumference,
regardless of its speed or orientation. -/
theorem circle_area_perimeter (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (orientation : Bool)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t))
    (c : Point) (r : ℝ) (hr : 0 < r) (hcircle : Γ = Metric.sphere c r) :
    (volume (jordanInterior Γ)).toReal = Real.pi * r ^ 2 ∧
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = 2 * Real.pi * r := by
  subst Γ
  have heq := circle_isoperimetric_equality γ hBV _ orientation hx c r hr rfl
  have hl := circle_perimeter_le γ c r hr orientation hx
  have ha := circle_area_lower_bound c r hr hx.2.1
  have hsq := pow_le_pow_left₀ ENNReal.toReal_nonneg hl 2
  have harea : (volume (jordanInterior (Metric.sphere c r))).toReal = Real.pi * r ^ 2 := by
    apply le_antisymm _ ha
    nlinarith [Real.pi_pos]
  refine ⟨harea, (sq_eq_sq₀ ENNReal.toReal_nonneg (by positivity)).mp ?_⟩
  rw [harea] at heq
  nlinarith [heq]

/-- Increasing affine normalization preserves the total variation on an interval. -/
theorem eVariationOn_affine_unit (γ : ℝ → Point) {a b : ℝ} (hab : a < b) :
    eVariationOn (fun t => γ (a + t * (b - a))) (Icc (0 : ℝ) 1) =
      eVariationOn γ (Icc a b) := by
  let u : ℝ → ℝ := fun t => a + t * (b - a)
  have hu : Monotone u := by
    intro s t hst
    dsimp [u]
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_right hst (sub_nonneg.mpr hab.le)) a
  have hc : Continuous u := continuous_const.add (continuous_id.mul continuous_const)
  have hi : u '' Icc (0 : ℝ) 1 = Icc a b := by
    simpa [u] using hc.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) (hu.monotoneOn _)
  simpa only [Function.comp_def, hi, u] using
    eVariationOn.comp_eq_of_monotoneOn γ u (hu.monotoneOn (Icc (0 : ℝ) 1))

/-- Affine normalization preserves the Jordan boundary and its winding orientation. -/
theorem oriented_jordan_affine_unit {a b : ℝ} (hab : a < b)
    (γ : ℝ → Point) (Γ : Set Point) (orientation : Bool)
    (hx : IsOrientedJordanParametrization hab.le Γ orientation
      (fun t : Icc a b => γ t)) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ orientation
      (fun t : Icc (0 : ℝ) 1 => γ (a + (t : ℝ) * (b - a))) := by
  obtain ⟨φ, hc, _, hs, hf⟩ :=
    Icc.exists_affine_monotone_surjection (by norm_num : (0 : ℝ) < 1) hab
  have hv (t : Icc (0 : ℝ) 1) : (φ t : ℝ) = a + (t : ℝ) * (b - a) := by
    simpa using hf t
  have hφa : φ ⟨0, by norm_num, by norm_num⟩ = ⟨a, le_rfl, hab.le⟩ := by
    apply Subtype.ext
    simp [hv]
  have hφb : φ ⟨1, by norm_num, by norm_num⟩ = ⟨b, hab.le, le_rfl⟩ := by
    apply Subtype.ext
    simp [hv]
  have hinj : Function.Injective φ := by
    intro s t heq
    have he := congrArg Subtype.val heq
    rw [hv, hv] at he
    apply Subtype.ext
    nlinarith [hab]
  have he : (fun t : Icc (0 : ℝ) 1 => γ (a + (t : ℝ) * (b - a))) =
      (fun t : Icc a b => γ t) ∘ φ := by
    funext t
    simp only [Function.comp_def, hv]
  rw [he]
  refine ⟨by norm_num, hx.2.1, hx.2.2.1.comp hc, ?_, ?_, ?_, ?_⟩
  · rw [Function.Surjective.range_comp hs, hx.2.2.2.1]
  · simpa only [Function.comp_def, hφa, hφb] using hx.2.2.2.2.1
  · intro s hss t htt hst
    apply hinj
    apply hx.2.2.2.2.2.1 _ _ hst
    · change (φ s : ℝ) < b
      rw [hv]
      have hh : (s : ℝ) < 1 := hss
      nlinarith [hab]
    · change (φ t : ℝ) < b
      rw [hv]
      have hh : (t : ℝ) < 1 := htt
      nlinarith [hab]
  · intro p hp
    have hw := hx.2.2.2.2.2.2 p hp
    have hn : curveWinding hab.le (fun t : Icc a b => γ t) p ≠ 0 := by
      rw [hw]
      cases orientation <;> norm_num
    rw [curveWinding_comp_of_endpoints hab.le (by norm_num : (0 : ℝ) ≤ 1)
      (exists_curveAngleLift_of_curveWinding_ne_zero hab.le hn) hc hφa hφb]
    exact hw

/-- The full rectifiable theorem on any nondegenerate compact parameter interval. -/
theorem jordan_isoperimetric_rectifiable_interval (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (orientation : Bool)
    (hx : IsOrientedJordanParametrization hab.le Γ orientation
      (fun t : Icc a b => γ t)) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hv := eVariationOn_affine_unit γ hab
  have hb : BoundedVariationOn (fun t => γ (a + t * (b - a))) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, hv] using hBV
  simpa only [hv] using jordan_isoperimetric_rectifiable_circle_iff
    (fun t => γ (a + t * (b - a))) hb Γ orientation
    (oriented_jordan_affine_unit hab γ Γ orientation hx)

/-- Exact circle formulas for arbitrary compact parameter intervals. -/
theorem circle_area_perimeter_interval (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (orientation : Bool)
    (hx : IsOrientedJordanParametrization hab.le Γ orientation
      (fun t : Icc a b => γ t))
    (c : Point) (r : ℝ) (hr : 0 < r) (hcircle : Γ = Metric.sphere c r) :
    (volume (jordanInterior Γ)).toReal = Real.pi * r ^ 2 ∧
      (eVariationOn γ (Icc a b)).toReal = 2 * Real.pi * r := by
  have hv := eVariationOn_affine_unit γ hab
  have hb : BoundedVariationOn (fun t => γ (a + t * (b - a))) (Icc (0 : ℝ) 1) := by
    simpa only [BoundedVariationOn, hv] using hBV
  simpa only [hv] using circle_area_perimeter
    (fun t => γ (a + t * (b - a))) hb Γ orientation
    (oriented_jordan_affine_unit hab γ Γ orientation hx) c r hr hcircle

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_area_perimeter
#check_upstream ClassicalTheorems.Progress.Isoperimetric.eVariationOn_affine_unit
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_affine_unit
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_rectifiable_interval
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_area_perimeter_interval

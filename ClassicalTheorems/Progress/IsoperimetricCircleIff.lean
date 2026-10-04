/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.CircleParametrization

/-! The equality characterization in the classical rectifiable isoperimetric
theorem: equality holds if and only if the boundary is a circle. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The circumference bounds the perimeter of either orientation of a simple
circle parametrization. Differentiability and speed conditions are unnecessary. -/
theorem circle_perimeter_le (γ : ℝ → Point) (c : Point) (r : ℝ) (hr : 0 < r)
    (orientation : Bool)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (Metric.sphere c r) orientation (fun t : Icc (0 : ℝ) 1 => γ t)) :
    (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ≤ 2 * Real.pi * r := by
  cases orientation with
  | true => exact circle_perimeter_le_counterclockwise γ c r hr hx
  | false =>
      let δ : ℝ → Point := fun t => γ (1 - t)
      have hv : eVariationOn δ (Icc (0 : ℝ) 1) = eVariationOn γ (Icc (0 : ℝ) 1) :=
        eVariationOn_reverse_unit γ
      have ho : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
          (Metric.sphere c r) true (fun t : Icc (0 : ℝ) 1 => δ t) := by
        simpa only [Bool.not_false, Function.comp_def, Icc.reverse, zero_add, δ] using
          oriented_jordan_reverse (fun t : Icc (0 : ℝ) 1 => γ t)
            (Metric.sphere c r) false hx
      simpa only [hv] using circle_perimeter_le_counterclockwise δ c r hr ho

/-- Every simple rectifiable Jordan parametrization of a circle attains the
sharp bound, in either orientation. -/
theorem circle_isoperimetric_equality (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (orientation : Bool)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t))
    (c : Point) (r : ℝ) (hr : 0 < r) (hcircle : Γ = Metric.sphere c r) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 := by
  subst Γ
  have hineq := (jordan_isoperimetric_rectifiable_any_orientation
    γ hBV (Metric.sphere c r) orientation hx).1
  have hlength := circle_perimeter_le γ c r hr orientation hx
  have harea := circle_area_lower_bound c r hr hx.2.1
  apply le_antisymm hineq
  calc
    (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ≤ (2 * Real.pi * r) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hlength 2
    _ = 4 * Real.pi * (Real.pi * r ^ 2) := by ring
    _ ≤ 4 * Real.pi * (volume (jordanInterior (Metric.sphere c r))).toReal :=
      mul_le_mul_of_nonneg_left harea (by positivity)

/-- The sharp isoperimetric inequality and its full equality characterization
for any continuous rectifiable Jordan parametrization, in either orientation. -/
theorem jordan_isoperimetric_rectifiable_circle_iff (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (orientation : Bool)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have h := jordan_isoperimetric_rectifiable_any_orientation γ hBV Γ orientation hx
  refine ⟨h.1, h.2, ?_⟩
  rintro ⟨c, r, hr, hc⟩
  exact circle_isoperimetric_equality γ hBV Γ orientation hx c r hr hc

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_perimeter_le
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_isoperimetric_equality
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_rectifiable_circle_iff

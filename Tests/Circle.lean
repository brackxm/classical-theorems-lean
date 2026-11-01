/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Isoperimetric
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic.NormNum

/-!
# A translated circle attaining the isoperimetric bound

The radius-3 circle centered at (2, -1) is traversed once on [0, 2π].
Its actual Jordan interior is the open disk, with Lebesgue area 9π and
total-variation perimeter 6π. The public Jordan isoperimetric theorem
must recognize this explicit simple closed rectifiable curve as an equality case.
-/

noncomputable section
open Set MeasureTheory

namespace ClassicalTheoremsTest.Circle

private abbrev chart : ℂ ≃ₗᵢ[ℝ] MovingSofa.Point := Complex.orthonormalBasisOneI.repr
private abbrev z : ℂ := 2 - Complex.I
private abbrev center : MovingSofa.Point := chart z
private def curve (t : ℝ) : MovingSofa.Point := chart (circleMap z 3 t)

private theorem rectifiable : BoundedVariationOn curve (Icc 0 (2 * Real.pi)) := by
  exact (chart.lipschitzWith.comp (lipschitzWith_circleMap z 3)).comp_boundedVariationOn
    (BoundedVariationOn.id_Icc 0 (2 * Real.pi))

private theorem continuous_curve : ContinuousOn curve (Icc 0 (2 * Real.pi)) :=
  (chart.continuous.comp (continuous_circleMap z 3)).continuousOn

private theorem covers_circle : curve '' Icc 0 (2 * Real.pi) = Metric.sphere center 3 := by
  have h : circleMap z 3 '' Icc 0 (2 * Real.pi) = Metric.sphere z 3 := by
    apply Subset.antisymm
    · rintro _ ⟨t, _, rfl⟩
      exact circleMap_mem_sphere z (by norm_num) t
    · have hsurj : circleMap z 3 '' Ioc 0 (2 * Real.pi) = Metric.sphere z 3 := by
        simp
      rw [← hsurj]
      exact image_mono Ioc_subset_Icc_self
  change (chart ∘ circleMap z 3) '' Icc 0 (2 * Real.pi) = _
  rw [image_comp, h, chart.image_sphere]

private theorem closed_curve : curve 0 = curve (2 * Real.pi) := by
  apply congrArg chart
  simpa only [zero_add] using ((periodic_circleMap z 3) 0).symm

private theorem simple_curve : InjOn curve (Ico 0 (2 * Real.pi)) := by
  intro s hs t ht h
  exact injOn_circleMap_of_abs_sub_le' (by norm_num : (3 : ℝ) ≠ 0)
    (by simp : 2 * Real.pi - 0 ≤ 2 * Real.pi) hs ht (chart.injective h)

/-- The bounded-component interpretation of the circular boundary is exactly the open disk. -/
theorem interior_is_disk :
    MovingSofa.jordanInterior (Metric.sphere center 3) = Metric.ball center 3 :=
  ClassicalTheorems.Progress.Isoperimetric.jordanInterior_sphere_eq_ball
    center 3 (by norm_num)

/-- Actual area and total variation have the expected radius scaling and normalization. -/
theorem area_and_perimeter :
    (volume (MovingSofa.jordanInterior (Metric.sphere center 3))).toReal = 9 * Real.pi ∧
    (eVariationOn curve (Icc 0 (2 * Real.pi))).toReal = 6 * Real.pi := by
  have h := ClassicalTheorems.circle_area_perimeter_unoriented
    curve Real.two_pi_pos rectifiable center 3 (by norm_num)
    continuous_curve covers_circle closed_curve simple_curve
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

/-- The indexed Jordan theorem accepts this explicit parametrization and gives equality. -/
theorem sharp_equality :
    4 * Real.pi * (volume (MovingSofa.jordanInterior (Metric.sphere center 3))).toReal =
      (eVariationOn curve (Icc 0 (2 * Real.pi))).toReal ^ 2 := by
  have h := ClassicalTheorems.isoperimetric_theorem_jordan
    curve Real.two_pi_pos rectifiable (Metric.sphere center 3)
    (ClassicalTheorems.Progress.Isoperimetric.sphere_isJordanCurve center 3 (by norm_num))
    continuous_curve covers_circle closed_curve simple_curve
  exact h.2.mpr ⟨center, 3, by norm_num, rfl⟩

#check_upstream interior_is_disk
#check_upstream area_and_perimeter
#check_upstream sharp_equality

end ClassicalTheoremsTest.Circle

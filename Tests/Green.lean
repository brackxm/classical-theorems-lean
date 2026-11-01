/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Green
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.NormNum

/-!
# Signed Green identities on a translated triangle with corners

For vertices (2, -1), (5, -1), (2, 3), the field P = -y, Q = 2x has curl 3.
Explicit edge integration gives 18 counterclockwise and -18 clockwise.
Green's theorem then recovers the geometric area 6 in both orientations.
The calibrated sign must work for every C¹ field, including the exact form
x dx + y dy, whose closed-boundary integral is zero.
-/

noncomputable section
open Set MeasureTheory
open ClassicalTheorems

namespace ClassicalTheoremsTest.Green

private abbrev a : Schoenflies.Plane := Schoenflies.Plane.mk 2 (-1)
private abbrev b : Schoenflies.Plane := Schoenflies.Plane.mk 5 (-1)
private abbrev c : Schoenflies.Plane := Schoenflies.Plane.mk 2 3

private theorem ccw_nondegenerate : Schoenflies.Plane.det (b - a) (c - a) ≠ 0 := by
  norm_num [a, b, c, Schoenflies.Plane.det, PiLp.sub_apply]

private theorem cw_nondegenerate : Schoenflies.Plane.det (c - a) (b - a) ≠ 0 := by
  norm_num [a, b, c, Schoenflies.Plane.det, PiLp.sub_apply]

private def ccw : Schoenflies.PrePolygon 0 := (Schoenflies.triangle ccw_nondegenerate).toPre
private def cw : Schoenflies.PrePolygon 0 := (Schoenflies.triangle cw_nondegenerate).toPre
private def p (z : ℂ) : ℝ := -z.im
private def q (z : ℂ) : ℝ := 2 * z.re

private theorem p_smooth : ContDiffOn ℝ 1 p univ :=
  (-Complex.imCLM).contDiff.contDiffOn

private theorem q_smooth : ContDiffOn ℝ 1 q univ :=
  ((2 : ℝ) • Complex.reCLM).contDiff.contDiffOn

-- Integrate the affine field on one straight edge independently of Green's theorem.
private theorem edge_integral (u v : ℂ) :
    (∫ t in (0 : ℝ)..1, -(AffineMap.lineMap u v t).im * (v - u).re +
      2 * (AffineMap.lineMap u v t).re * (v - u).im) =
      (v.re - u.re) * (v.im - u.im) / 2 -
        u.im * (v.re - u.re) + 2 * u.re * (v.im - u.im) := by
  have he : (fun t : ℝ => -(AffineMap.lineMap u v t).im * (v - u).re +
      2 * (AffineMap.lineMap u v t).re * (v - u).im) =
      fun t => ((v.re - u.re) * (v.im - u.im)) * t +
        (-u.im * (v.re - u.re) + 2 * u.re * (v.im - u.im)) := by
    funext t
    simp [AffineMap.lineMap_apply]
    ring
  rw [he, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  norm_num
  ring

/-- Both field components contribute to the counterclockwise integral 18. -/
theorem counterclockwise_integral : polygonLineIntegral ccw p q = 18 := by
  simp only [polygonLineIntegral, p, q, polygonEdge]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  rw [edge_integral, edge_integral, edge_integral]
  norm_num [ccw, polygonVertex, Schoenflies.triangle, Schoenflies.ClosedPolygon.toPre,
    Complex.orthonormalBasisOneI_repr_symm_apply, a, b, c]

/-- Reversing the three vertices reverses the actual signed boundary integral. -/
theorem clockwise_integral : polygonLineIntegral cw p q = -18 := by
  simp only [polygonLineIntegral, p, q, polygonEdge]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]
  rw [edge_integral, edge_integral, edge_integral]
  norm_num [cw, polygonVertex, Schoenflies.triangle, Schoenflies.ClosedPolygon.toPre,
    Complex.orthonormalBasisOneI_repr_symm_apply, a, b, c]

private theorem curl_integral (poly : Schoenflies.PrePolygon 0) :
    (∫ z in polygonInterior poly, fderiv ℝ q z (1 : ℂ) - fderiv ℝ p z Complex.I) =
      3 * (volume (polygonInterior poly)).toReal := by
  have hd : (fun z : ℂ => fderiv ℝ q z (1 : ℂ) - fderiv ℝ p z Complex.I) =
      fun _ => (3 : ℝ) := by
    funext z
    change (fderiv ℝ ((2 : ℝ) • Complex.reCLM : ℂ →L[ℝ] ℝ) z) 1 -
      (fderiv ℝ (-Complex.imCLM : ℂ →L[ℝ] ℝ) z) Complex.I = 3
    rw [ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
    norm_num
  rw [hd, integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  change (volume (polygonInterior poly)).toReal * 3 = 3 * (volume (polygonInterior poly)).toReal
  ring

private theorem area_from_integral (poly : Schoenflies.PrePolygon 0)
    (h : |polygonLineIntegral poly p q| = 18) :
    (volume (polygonInterior poly)).toReal = 6 := by
  have hg := greens_theorem_polygon_abs poly univ isOpen_univ (subset_univ _)
    p q p_smooth q_smooth
  rw [h, curl_integral, abs_of_nonneg (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)] at hg
  linarith

/-- Green recovers the actual interior area, independently of vertex order. -/
theorem area_preserved :
    (volume (polygonInterior ccw)).toReal = 6 ∧
    (volume (polygonInterior cw)).toReal = 6 := by
  constructor
  · apply area_from_integral
    rw [counterclockwise_integral]
    norm_num
  · apply area_from_integral
    rw [clockwise_integral]
    norm_num

-- The polygon theorem supplies one orientation for all fields. Determine it
-- from the independently computed nonzero field integral, rather than assuming it.
private theorem calibrated_green (poly : Schoenflies.PrePolygon 0) (sign : ℝ)
    (hline : polygonLineIntegral poly p q = sign * 18)
    (harea : (volume (polygonInterior poly)).toReal = 6)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P univ) (hQ : ContDiffOn ℝ 1 Q univ) :
    polygonLineIntegral poly P Q = sign *
      ∫ z in polygonInterior poly, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_polygon poly univ isOpen_univ (subset_univ _)
  have hc := hg p q p_smooth q_smooth
  rw [hline, curl_integral, harea] at hc
  have hs : (if orientation then (1 : ℝ) else -1) = sign := by linarith
  rw [hg P Q hP hQ, hs]

/-- The positive signed identity holds for every C¹ field on this triangle. -/
theorem counterclockwise_green (P Q : ℂ → ℝ)
    (hP : ContDiffOn ℝ 1 P univ) (hQ : ContDiffOn ℝ 1 Q univ) :
    polygonLineIntegral ccw P Q =
      ∫ z in polygonInterior ccw, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  simpa using calibrated_green ccw 1 (by simpa using counterclockwise_integral)
    area_preserved.1 P Q hP hQ

/-- The negative signed identity holds for every C¹ field on the reversed triangle. -/
theorem clockwise_green (P Q : ℂ → ℝ)
    (hP : ContDiffOn ℝ 1 P univ) (hQ : ContDiffOn ℝ 1 Q univ) :
    polygonLineIntegral cw P Q =
      -(∫ z in polygonInterior cw, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I) := by
  simpa using calibrated_green cw (-1) (by simpa using clockwise_integral)
    area_preserved.2 P Q hP hQ

/-- The exact form x dx + y dy integrates to zero in either orientation. -/
theorem exact_field_zero :
    polygonLineIntegral ccw Complex.re Complex.im = 0 ∧
    polygonLineIntegral cw Complex.re Complex.im = 0 := by
  have hd : (fun z : ℂ => fderiv ℝ Complex.im z (1 : ℂ) -
      fderiv ℝ Complex.re z Complex.I) = fun _ => (0 : ℝ) := by
    funext z
    change (fderiv ℝ (Complex.imCLM : ℂ →L[ℝ] ℝ) z) 1 -
      (fderiv ℝ (Complex.reCLM : ℂ →L[ℝ] ℝ) z) Complex.I = 0
    simp [ContinuousLinearMap.fderiv]
  constructor
  · rw [counterclockwise_green Complex.re Complex.im Complex.reCLM.contDiff.contDiffOn
      Complex.imCLM.contDiff.contDiffOn, hd]
    simp
  · rw [clockwise_green Complex.re Complex.im Complex.reCLM.contDiff.contDiffOn
      Complex.imCLM.contDiff.contDiffOn, hd]
    simp

#check_upstream counterclockwise_integral
#check_upstream clockwise_integral
#check_upstream area_preserved
#check_upstream counterclockwise_green
#check_upstream clockwise_green
#check_upstream exact_field_zero

end ClassicalTheoremsTest.Green

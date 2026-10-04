/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricOrientation
import MovingSofa.Curve.Jordan.Separation
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Circular boundaries attain the sharp isoperimetric bound, independently of
their simple rectifiable parametrization. -/

noncomputable section
open MeasureTheory Set MovingSofa
open scoped ENNReal
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The open disk lies in the bounded-component interior of its boundary circle. -/
theorem ball_subset_jordanInterior_sphere (c : Point) (r : ℝ) :
    Metric.ball c r ⊆ jordanInterior (Metric.sphere c r) := by
  intro p hp
  have hpout : p ∈ (Metric.sphere c r)ᶜ := by
    exact ne_of_lt (Metric.mem_ball.mp hp)
  refine ⟨hpout, ?_⟩
  have hsub : connectedComponentIn (Metric.sphere c r)ᶜ p ⊆ Metric.ball c r := by
    intro q hq
    by_contra hnot
    have hqr : r ≤ dist q c := le_of_not_gt (fun h => hnot (Metric.mem_ball.mpr h))
    obtain ⟨z, hz, he⟩ := isPreconnected_connectedComponentIn.intermediate_value
      (mem_connectedComponentIn hpout) hq (continuous_id.dist continuous_const).continuousOn
      ⟨(Metric.mem_ball.mp hp).le, hqr⟩
    have hzout := connectedComponentIn_subset (Metric.sphere c r)ᶜ p hz
    exact hzout (Metric.mem_sphere.mpr he)
  exact (Metric.isBounded_ball (x := c) (r := r)).subset hsub

/-- Jordan separation supplies finiteness of the geometric interior's area. -/
theorem jordanInterior_isBounded {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    Bornology.IsBounded (jordanInterior Γ) := by
  obtain ⟨U, V, -, -, -, -, hUb, hVu, -, hcover, -, -, -, hVc⟩ := jordan_separation hΓ
  apply hUb.subset
  intro p hp
  rcases hcover.symm.subset hp.1 with h | h
  · exact h
  · exact False.elim (hVu (hVc p h ▸ hp.2))

/-- The geometric interior of a Jordan circle has at least the disk's area. -/
theorem circle_area_lower_bound (c : Point) (r : ℝ) (hr : 0 < r)
    (hΓ : IsJordanCurve (Metric.sphere c r)) :
    Real.pi * r ^ 2 ≤ (volume (jordanInterior (Metric.sphere c r))).toReal := by
  have hfin : volume (jordanInterior (Metric.sphere c r)) ≠ ∞ :=
    (jordanInterior_isBounded hΓ).measure_lt_top.ne
  have hle := ENNReal.toReal_mono hfin
    (measure_mono (ball_subset_jordanInterior_sphere c r))
  rw [EuclideanSpace.volume_ball_fin_two] at hle
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr.le, ENNReal.toReal_ofReal Real.pi_nonneg, mul_comm] using hle

/-- The angular circle map has sharp Lipschitz constant equal to its radius. -/
theorem circle_map_lipschitz (c : Point) (r : ℝ) (hr : 0 < r) :
    LipschitzWith r.toNNReal (fun θ : ℝ =>
      c + r • Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)) := by
  let T : ℂ ≃ₗᵢ[ℝ] Point := Complex.orthonormalBasisOneI.repr
  let z : ℝ → ℂ := fun θ => Real.cos θ + Real.sin θ * Complex.I
  have hz (θ : ℝ) : HasDerivAt z
      ((-(Real.sin θ : ℂ)) + (Real.cos θ : ℂ) * Complex.I) θ := by
    simpa only [z, Complex.ofReal_neg, Pi.add_apply] using!
      (Real.hasDerivAt_cos θ).ofReal_comp.add
        ((Real.hasDerivAt_sin θ).ofReal_comp.mul_const Complex.I)
  have hn (θ : ℝ) : ‖(-(Real.sin θ : ℂ)) + (Real.cos θ : ℂ) * Complex.I‖ = 1 := by
    have he : (-(Real.sin θ : ℂ)) + (Real.cos θ : ℂ) * Complex.I = Complex.I * z θ := by
      dsimp only [z]
      rw [mul_add, ← mul_assoc, mul_comm Complex.I (Real.sin θ : ℂ),
        mul_assoc, Complex.I_mul_I]
      ring
    rw [he, norm_mul, Complex.norm_I, one_mul]
    dsimp only [z]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]
    exact Complex.norm_cos_add_sin_mul_I θ
  have hd (θ : ℝ) : HasDerivAt (fun t => c + r • T (z t))
      (r • T ((-(Real.sin θ : ℂ)) + (Real.cos θ : ℂ) * Complex.I)) θ :=
    ((T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt θ (hz θ)).const_smul r).const_add c
  apply lipschitzWith_of_nnnorm_deriv_le (fun θ => (hd θ).differentiableAt)
  intro θ
  rw [(hd θ).deriv]
  apply NNReal.coe_le_coe.mp
  simpa only [coe_nnnorm, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    T.norm_map, hn, mul_one, Real.coe_toNNReal _ hr.le] using (le_refl r)

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ball_subset_jordanInterior_sphere
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordanInterior_isBounded
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_area_lower_bound
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_map_lipschitz

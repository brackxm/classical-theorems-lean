/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! The sharp periodic Poincaré (Wirtinger) inequality, for the analytic step of classical isoperimetry.
The Fourier expansion and derivative identity are proved in mathlib; neither is
assumed as an extra hypothesis here. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem continuous_memLp_two (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc 0 1)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).2
  exact ((hf.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc).mono_set
    Ioc_subset_Icc_self

/-- The sharp unit-period inequality, with the constant Fourier mode removed. -/
theorem wirtinger_complex (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hclosed : f 0 = f 1) (hmean : (∫ t in (0 : ℝ)..1, f t) = 0) :
    4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, ‖f t‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..1, ‖deriv f t‖ ^ 2 := by
  let hab : (0 : ℝ) < 1 := by norm_num
  have hc0 : fourierCoeffOn hab f 0 = 0 := by
    simp [fourierCoeffOn_eq_integral, hmean]
  have hcoeff (n : ℤ) :
      4 * Real.pi ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 ≤
        ‖fourierCoeffOn hab (deriv f) n‖ ^ 2 := by
    by_cases hn : n = 0
    · subst n
      rw [hc0]
      simp
    have hd := fourierCoeffOn_of_hasDerivAt hab hn
      (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt)
      (hf.continuous_deriv_one.intervalIntegrable 0 1)
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have heq : fourierCoeffOn hab (deriv f) n =
        (2 * Real.pi * Complex.I * n) * fourierCoeffOn hab f n := by
      simp only [hclosed, sub_self, mul_zero, zero_sub, Complex.ofReal_one,
        Complex.ofReal_zero, sub_zero, one_mul] at hd
      field_simp at hd
      linear_combination -hd
    have hnsq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : (1 : ℤ) ≤ n ^ 2 := by
        rcases Int.le_total n 0 with h | h
        · have : n ≤ -1 := by omega
          nlinarith
        · have : 1 ≤ n := by omega
          nlinarith
      exact_mod_cast h
    rw [heq, norm_mul, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, mul_one,
      Complex.norm_intCast]
    have hpi : ‖Real.pi‖ = Real.pi := Real.norm_of_nonneg Real.pi_pos.le
    rw [hpi]
    calc
      4 * Real.pi ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2 ≤
          4 * Real.pi ^ 2 * ((n : ℝ) ^ 2 * ‖fourierCoeffOn hab f n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr hnsq)
          (sq_nonneg ‖fourierCoeffOn hab f n‖)]
      _ = (2 * Real.pi * |(n : ℝ)| * ‖fourierCoeffOn hab f n‖) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, sq_abs]
        ring
  have hs := (hasSum_sq_fourierCoeffOn hab (continuous_memLp_two f hf.continuous)).mul_left
    (4 * Real.pi ^ 2)
  have hs' := hasSum_sq_fourierCoeffOn hab
    (continuous_memLp_two (deriv f) hf.continuous_deriv_one)
  simpa using hasSum_le hcoeff hs hs'

theorem wirtinger_real (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hclosed : f 0 = f 1) (hmean : (∫ t in (0 : ℝ)..1, f t) = 0) :
    4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, f t ^ 2) ≤
      ∫ t in (0 : ℝ)..1, deriv f t ^ 2 := by
  have hc : ContDiff ℝ 1 (fun t => (f t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hf
  have hd (t : ℝ) : deriv (fun s => (f s : ℂ)) t = ((deriv f t : ℝ) : ℂ) :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (hf.differentiable one_ne_zero t).hasDerivAt).deriv
  have hm : (∫ t in (0 : ℝ)..1, (f t : ℂ)) = 0 := by
    rw [intervalIntegral.integral_ofReal, hmean]
    simp
  simpa only [hd, Complex.norm_real, Real.norm_eq_abs, sq_abs] using
    wirtinger_complex (fun t => (f t : ℂ)) hc (congrArg Complex.ofReal hclosed) hm

/-- The sharp inequality for a closed function after subtracting its mean. -/
theorem wirtinger_centered (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hclosed : f 0 = f 1) :
    4 * Real.pi ^ 2 *
        (∫ t in (0 : ℝ)..1, (f t - ∫ s in (0 : ℝ)..1, f s) ^ 2) ≤
      ∫ t in (0 : ℝ)..1, deriv f t ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, f t
  have hd (t : ℝ) : deriv (fun s => f s - m) t = deriv f t :=
    ((hf.differentiable one_ne_zero t).hasDerivAt.sub_const m).deriv
  have hm : (∫ t in (0 : ℝ)..1, f t - m) = 0 := by
    rw [intervalIntegral.integral_sub (hf.continuous.intervalIntegrable 0 1)
      (intervalIntegrable_const), intervalIntegral.integral_const]
    simp [m]
  simpa only [hd] using wirtinger_real (fun t => f t - m) (hf.sub contDiff_const)
    (by rw [hclosed]) hm

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.wirtinger_complex
#check_upstream ClassicalTheorems.Progress.Isoperimetric.wirtinger_centered

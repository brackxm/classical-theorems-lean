/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricClassical
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! The analytic isoperimetric estimate for absolutely continuous coordinates.
This supplies the nonsmooth analytic step used by `IsoperimetricRectifiable`
and the arc-length reparametrization in `RectifiableReparametrization`. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

/-- Integration by parts against a complex C¹ test function. -/
theorem ac_complex_ibp (f : ℝ → ℝ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (g : ℝ → ℂ) (hg : ContDiff ℝ 1 g) :
    (∫ t in (0 : ℝ)..1, (f t : ℂ) * deriv g t) =
      (f 1 : ℂ) * g 1 - (f 0 : ℂ) * g 0 -
        ∫ t in (0 : ℝ)..1, ((deriv f t : ℝ) : ℂ) * g t := by
  have hgr : ContDiff ℝ 1 (fun t => (g t).re) := Complex.reCLM.contDiff.comp hg
  have hgi : ContDiff ℝ 1 (fun t => (g t).im) := Complex.imCLM.contDiff.comp hg
  have hr := hf.integral_mul_deriv_eq_deriv_mul hgr.contDiffOn.absolutelyContinuousOnInterval
  have hi := hf.integral_mul_deriv_eq_deriv_mul hgi.contDiffOn.absolutelyContinuousOnInterval
  have hfi : IntervalIntegrable (fun t => (f t : ℂ)) volume 0 1 :=
    (Complex.continuous_ofReal.comp_continuousOn hf.continuousOn).intervalIntegrable
  have hdi : IntervalIntegrable (fun t => ((deriv f t : ℝ) : ℂ)) volume 0 1 :=
    ⟨hf.intervalIntegrable_deriv.1.ofReal, hf.intervalIntegrable_deriv.2.ofReal⟩
  have hleft := hfi.mul_continuousOn hg.continuous_deriv_one.continuousOn
  have hright := hdi.mul_continuousOn hg.continuous.continuousOn
  have hrl : (∫ t in (0 : ℝ)..1, (f t : ℂ) * deriv g t).re =
      ∫ t in (0 : ℝ)..1, ((f t : ℂ) * deriv g t).re := by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm hleft).symm
  have hrr : (∫ t in (0 : ℝ)..1, ((deriv f t : ℝ) : ℂ) * g t).re =
      ∫ t in (0 : ℝ)..1, (((deriv f t : ℝ) : ℂ) * g t).re := by
    simpa using (Complex.reCLM.intervalIntegral_comp_comm hright).symm
  have hil : (∫ t in (0 : ℝ)..1, (f t : ℂ) * deriv g t).im =
      ∫ t in (0 : ℝ)..1, ((f t : ℂ) * deriv g t).im := by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hleft).symm
  have hir : (∫ t in (0 : ℝ)..1, ((deriv f t : ℝ) : ℂ) * g t).im =
      ∫ t in (0 : ℝ)..1, (((deriv f t : ℝ) : ℂ) * g t).im := by
    simpa using (Complex.imCLM.intervalIntegral_comp_comm hright).symm
  apply Complex.ext
  · rw [hrl, Complex.sub_re, Complex.sub_re, hrr]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, Green.deriv_re g hg, Complex.reCLM_apply] using hr
  · rw [hil, Complex.sub_im, Complex.sub_im, hir]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Green.deriv_im g hg, Complex.imCLM_apply] using hi

/-- Fourier integration by parts for an absolutely continuous real function. -/
theorem ac_fourier_derivative (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hclosed : f 0 = f 1) (n : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun t => ((deriv f t : ℝ) : ℂ)) n =
      (2 * Real.pi * Complex.I * n) *
        fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (fun t => (f t : ℂ)) n := by
  let g := fun t : ℝ => fourier (-n) (t : AddCircle (1 : ℝ))
  have hg : ContDiff ℝ 1 g := by
    simp only [g, fourier_coe_apply, Complex.ofReal_one, div_one]
    exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hd (t : ℝ) : deriv g t = (-2 * Real.pi * Complex.I * n) * g t := by
    simpa only [Complex.ofReal_one, div_one] using (hasDerivAt_fourier_neg (1 : ℝ) n t).deriv
  have hg1 : g 1 = g 0 := by
    change fourier (-n) ((1 : ℝ) : AddCircle (1 : ℝ)) = fourier (-n) ((0 : ℝ) : AddCircle (1 : ℝ))
    congr 1
    simp
  have hi := ac_complex_ibp f hf g hg
  simp only [hd] at hi
  have hre : (∫ t in (0 : ℝ)..1, (f t : ℂ) * ((-2 * Real.pi * Complex.I * n) * g t)) =
      (-2 * Real.pi * Complex.I * n) * ∫ t in (0 : ℝ)..1, g t * (f t : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  rw [hre, hg1, hclosed, sub_self, zero_sub] at hi
  simp only [fourierCoeffOn_eq_integral, sub_zero, one_div,
    inv_one, one_smul, smul_eq_mul]
  have hswap : (∫ t in (0 : ℝ)..1, ((deriv f t : ℝ) : ℂ) * g t) =
      ∫ t in (0 : ℝ)..1, g t * ((deriv f t : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hswap] at hi
  have hfinal : (∫ t in (0 : ℝ)..1, g t * ((deriv f t : ℝ) : ℂ)) =
      (2 * Real.pi * Complex.I * n) * ∫ t in (0 : ℝ)..1, g t * (f t : ℂ) := by
    linear_combination hi
  simpa only [g, fourier_coe_apply, sub_zero, Complex.ofReal_one, div_one] using hfinal


/-- The sharp periodic Wirtinger inequality for absolutely continuous functions
whose a.e. derivative is square integrable. -/
theorem wirtinger_ac (f : ℝ → ℝ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hclosed : f 0 = f 1) (hmean : (∫ t in (0 : ℝ)..1, f t) = 0)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 1))) :
    4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, f t ^ 2) ≤
      ∫ t in (0 : ℝ)..1, deriv f t ^ 2 := by
  let hab : (0 : ℝ) < 1 := by norm_num
  let F := fun t => (f t : ℂ)
  let D := fun t => ((deriv f t : ℝ) : ℂ)
  have hfc : ContinuousOn f (Icc (0 : ℝ) 1) := by simpa using hf.continuousOn
  have hfm : MemLp f 2 (volume.restrict (Ioc 0 1)) := by
    apply (memLp_two_iff_integrable_sq
      ((hfc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).2
    exact ((hfc.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hFm : MemLp F 2 (volume.restrict (Ioc 0 1)) := hfm.ofReal
  have hDm : MemLp D 2 (volume.restrict (Ioc 0 1)) := hd.ofReal
  have hc0 : fourierCoeffOn hab F 0 = 0 := by
    simp [F, fourierCoeffOn_eq_integral, intervalIntegral.integral_ofReal, hmean]
  have hcoeff (n : ℤ) :
      4 * Real.pi ^ 2 * ‖fourierCoeffOn hab F n‖ ^ 2 ≤
        ‖fourierCoeffOn hab D n‖ ^ 2 := by
    by_cases hn : n = 0
    · subst n
      rw [hc0]
      simp
    have heq : fourierCoeffOn hab D n =
        (2 * Real.pi * Complex.I * n) * fourierCoeffOn hab F n :=
      ac_fourier_derivative f hf hclosed n
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
      Complex.norm_intCast, Real.norm_of_nonneg Real.pi_pos.le]
    calc
      _ ≤ 4 * Real.pi ^ 2 * ((n : ℝ) ^ 2 * ‖fourierCoeffOn hab F n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr hnsq) (sq_nonneg ‖fourierCoeffOn hab F n‖)]
      _ = _ := by rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
  have hs := (hasSum_sq_fourierCoeffOn hab hFm).mul_left (4 * Real.pi ^ 2)
  have hs' := hasSum_sq_fourierCoeffOn hab hDm
  simpa only [F, D, Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero,
    inv_one, one_smul] using hasSum_le hcoeff hs hs'

/-- Subtracting the mean gives the sharp absolutely continuous Wirtinger bound. -/
theorem wirtinger_ac_centered (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1) (hclosed : f 0 = f 1)
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 1))) :
    4 * Real.pi ^ 2 *
        (∫ t in (0 : ℝ)..1, (f t - ∫ s in (0 : ℝ)..1, f s) ^ 2) ≤
      ∫ t in (0 : ℝ)..1, deriv f t ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, f t
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => m) 0 1 :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hm : (∫ t in (0 : ℝ)..1, f t - m) = 0 := by
    rw [intervalIntegral.integral_sub hf.continuousOn.intervalIntegrable intervalIntegrable_const]
    simp [m]
  have hd' : MemLp (deriv (fun t => f t - m)) 2 (volume.restrict (Ioc 0 1)) := by
    simpa only [deriv_sub_const_fun] using hd
  simpa only [deriv_sub_const] using wirtinger_ac (fun t => f t - m) (hf.sub hconst)
    (by rw [hclosed]) hm hd'


/-- The sharp area–energy bound does not require continuous derivatives. -/
theorem signed_area_le_energy_ac (x y : ℝ → ℝ)
    (hx : AbsolutelyContinuousOnInterval x 0 1)
    (hy : AbsolutelyContinuousOnInterval y 0 1)
    (hxclosed : x 0 = x 1) (hyclosed : y 0 = y 1)
    (hdx : MemLp (deriv x) 2 (volume.restrict (Ioc 0 1)))
    (hdy : MemLp (deriv y) 2 (volume.restrict (Ioc 0 1))) :
    4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) ≤
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, x t
  let X := fun t => x t - m
  have hX : ContinuousOn X (uIcc (0 : ℝ) 1) := hx.continuousOn.sub continuousOn_const
  have hiX : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 :=
    (hX.pow 2).intervalIntegrable
  have hidx : IntervalIntegrable (fun t => deriv x t ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable).mp hdx
  have hidy : IntervalIntegrable (fun t => deriv y t ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (memLp_two_iff_integrable_sq hdy.aestronglyMeasurable).mp hdy
  have hiy : (∫ t in (0 : ℝ)..1, deriv y t) = 0 := by
    rw [hy.integral_deriv_eq_sub, hyclosed, sub_self]
  have hixy : IntervalIntegrable (fun t => x t * deriv y t) volume 0 1 :=
    hy.intervalIntegrable_deriv.continuousOn_mul hx.continuousOn
  have hiXy : IntervalIntegrable (fun t => X t * deriv y t) volume 0 1 :=
    hy.intervalIntegrable_deriv.continuousOn_mul hX
  have harea : (∫ t in (0 : ℝ)..1, X t * deriv y t) =
      ∫ t in (0 : ℝ)..1, x t * deriv y t := by
    have himy : IntervalIntegrable (fun t => m * deriv y t) volume 0 1 :=
      hy.intervalIntegrable_deriv.const_mul m
    simp only [X, sub_mul]
    rw [intervalIntegral.integral_sub hixy himy,
      intervalIntegral.integral_const_mul, hiy, mul_zero, sub_zero]
  have hbound :
      4 * Real.pi * (∫ t in (0 : ℝ)..1, X t * deriv y t) ≤
        4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) +
          (∫ t in (0 : ℝ)..1, deriv y t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hiX.const_mul _) hidy]
    apply intervalIntegral.integral_mono_on (by norm_num) (hiXy.const_mul _)
      ((hiX.const_mul _).add hidy)
    intro t _
    change 4 * Real.pi * (X t * deriv y t) ≤ 4 * Real.pi ^ 2 * X t ^ 2 + deriv y t ^ 2
    nlinarith [sq_nonneg (2 * Real.pi * X t - deriv y t)]
  rw [harea] at hbound
  rw [intervalIntegral.integral_add hidx hidy]
  exact hbound.trans (add_le_add (wirtinger_ac_centered x hx hxclosed hdx) le_rfl)

/-- A closed absolutely continuous curve with bounded a.e. speed has the sharp
area bound. No differentiability is required at exceptional points such as corners. -/
theorem signed_area_le_speed_bound_ac (x y : ℝ → ℝ)
    (hx : AbsolutelyContinuousOnInterval x 0 1)
    (hy : AbsolutelyContinuousOnInterval y 0 1)
    (hxclosed : x 0 = x 1) (hyclosed : y 0 = y 1) (L : ℝ)
    (hspeed : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv x t ^ 2 + deriv y t ^ 2 ≤ L ^ 2) :
    4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) ≤ L ^ 2 := by
  have hdx : MemLp (deriv x) 2 (volume.restrict (Ioc 0 1)) := by
    apply MemLp.of_bound (aestronglyMeasurable_deriv x _) |L|
    filter_upwards [hspeed] with t ht
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv y t), sq_abs (deriv x t), sq_abs L, abs_nonneg (deriv x t), abs_nonneg L]
  have hdy : MemLp (deriv y) 2 (volume.restrict (Ioc 0 1)) := by
    apply MemLp.of_bound (aestronglyMeasurable_deriv y _) |L|
    filter_upwards [hspeed] with t ht
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (deriv x t), sq_abs (deriv y t), sq_abs L, abs_nonneg (deriv y t), abs_nonneg L]
  apply (signed_area_le_energy_ac x y hx hy hxclosed hyclosed hdx hdy).trans
  have hi : IntervalIntegrable (fun t => deriv x t ^ 2 + deriv y t ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ((memLp_two_iff_integrable_sq hdx.aestronglyMeasurable).mp hdx).add
      ((memLp_two_iff_integrable_sq hdy.aestronglyMeasurable).mp hdy)
  have hspeedcc := hspeed
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hspeedcc
  calc
    _ ≤ ∫ _t in (0 : ℝ)..1, L ^ 2 :=
      intervalIntegral.integral_mono_ae_restrict (by norm_num) hi intervalIntegrable_const hspeedcc
    _ = L ^ 2 := by simp

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ac_complex_ibp
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ac_fourier_derivative
#check_upstream ClassicalTheorems.Progress.Isoperimetric.wirtinger_ac
#check_upstream ClassicalTheorems.Progress.Isoperimetric.wirtinger_ac_centered
#check_upstream ClassicalTheorems.Progress.Isoperimetric.signed_area_le_energy_ac
#check_upstream ClassicalTheorems.Progress.Isoperimetric.signed_area_le_speed_bound_ac

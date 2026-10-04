/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricACArea
import ClassicalTheorems.Progress.IsoperimetricC1Equality

/-! Equality in the sharp area-energy bound for Lipschitz curves. -/

noncomputable section
open MeasureTheory Set MovingSofa Filter
open scoped Topology
namespace ClassicalTheorems.Progress.Isoperimetric

theorem area_energy_defect_bound_ac (x y : ℝ → ℝ) (hx : AbsolutelyContinuousOnInterval x 0 1)
    (hy : AbsolutelyContinuousOnInterval y 0 1) (hxc : x 0 = x 1) (hyc : y 0 = y 1)
    (hdx : MemLp (deriv x) 2 (volume.restrict (Ioc 0 1)))
    (hdy : MemLp (deriv y) 2 (volume.restrict (Ioc 0 1))) :
    (∫ t in (0 : ℝ)..1,
      (2 * Real.pi * (x t - ∫ s in (0 : ℝ)..1, x s) - deriv y t) ^ 2) ≤
      (∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) := by
  let m := ∫ t in (0 : ℝ)..1, x t
  let X := fun t => x t - m
  have hX : ContinuousOn X (uIcc (0 : ℝ) 1) := hx.continuousOn.sub continuousOn_const
  have hiX : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 := (hX.pow 2).intervalIntegrable
  have hidx : IntervalIntegrable (fun t => deriv x t ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (memLp_two_iff_integrable_sq hdx.aestronglyMeasurable).mp hdx
  have hidy : IntervalIntegrable (fun t => deriv y t ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (memLp_two_iff_integrable_sq hdy.aestronglyMeasurable).mp hdy
  have hixy : IntervalIntegrable (fun t => X t * deriv y t) volume 0 1 := hy.intervalIntegrable_deriv.continuousOn_mul hX
  have harea : (∫ t in (0 : ℝ)..1, X t * deriv y t) = ∫ t in (0 : ℝ)..1, x t * deriv y t := by
    have hiy : (∫ t in (0 : ℝ)..1, deriv y t) = 0 := by
      rw [hy.integral_deriv_eq_sub, hyc, sub_self]
    have hi : IntervalIntegrable (fun t => x t * deriv y t) volume 0 1 :=
      hy.intervalIntegrable_deriv.continuousOn_mul hx.continuousOn
    have hi' : IntervalIntegrable (fun t => m * deriv y t) volume 0 1 :=
      hy.intervalIntegrable_deriv.const_mul m
    simp only [X, sub_mul]
    rw [intervalIntegral.integral_sub hi hi', intervalIntegral.integral_const_mul,
      hiy, mul_zero, sub_zero]
  have hid : (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) =
      4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) +
        (∫ t in (0 : ℝ)..1, deriv y t ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (4 * Real.pi ^ 2 * X t ^ 2 + deriv y t ^ 2) -
          4 * Real.pi * (X t * deriv y t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hiX.const_mul _).add hidy) (hixy.const_mul _),
          intervalIntegral.integral_add (hiX.const_mul _) hidy,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, harea]
  change (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) ≤ _
  rw [hid, intervalIntegral.integral_add hidx hidy]
  have hw := wirtinger_ac_centered x hx hxc hdx
  change 4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) ≤ _ at hw
  linarith


/-- Equality kills the completed-square defect almost everywhere. -/
theorem area_energy_equality_coordinate_ac (x y : ℝ → ℝ)
    (hx : AbsolutelyContinuousOnInterval x 0 1)
    (hy : AbsolutelyContinuousOnInterval y 0 1) (hxc : x 0 = x 1) (hyc : y 0 = y 1)
    (hdx : MemLp (deriv x) 2 (volume.restrict (Ioc 0 1)))
    (hdy : MemLp (deriv y) 2 (volume.restrict (Ioc 0 1)))
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) =
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2) :
    ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv y t = 2 * Real.pi * (x t - ∫ s in (0 : ℝ)..1, x s) := by
  let X := fun t => x t - ∫ s in (0 : ℝ)..1, x s
  let d := fun t => 2 * Real.pi * X t - deriv y t
  have hXu : ContinuousOn X (uIcc (0 : ℝ) 1) := hx.continuousOn.sub continuousOn_const
  have hX : ContinuousOn X (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hXu
  have hXm : MemLp X 2 (volume.restrict (Ioc 0 1)) := by
    apply (memLp_two_iff_integrable_sq
      ((hX.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)).2
    exact ((hX.pow 2).integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hdm : MemLp d 2 (volume.restrict (Ioc 0 1)) := (hXm.const_mul _).sub hdy
  have hdi : Integrable (fun t => d t ^ 2) (volume.restrict (Ioc 0 1)) :=
    (memLp_two_iff_integrable_sq hdm.aestronglyMeasurable).mp hdm
  have hb := area_energy_defect_bound_ac x y hx hy hxc hyc hdx hdy
  rw [heq, sub_self] at hb
  have hz : (∫ t in Ioc (0 : ℝ) 1, d t ^ 2) = 0 := by
    apply le_antisymm
    · change (∫ t in (0 : ℝ)..1, d t ^ 2) ≤ 0 at hb
      rwa [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hb
    · exact integral_nonneg (fun _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg (d t)) hdi).mp hz
  filter_upwards [hae] with t ht
  exact (sub_eq_zero.mp (sq_eq_zero_iff.mp ht)).symm

/-- Bounded Lipschitz derivatives are square integrable on the unit interval. -/
theorem lipschitz_deriv_memLp_two (f : ℝ → ℝ) (K : NNReal) (hf : LipschitzWith K f) :
    MemLp (deriv f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  MemLp.of_bound (aestronglyMeasurable_deriv f _) K
    (Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hf))

/-- Area-energy equality makes a Lipschitz curve satisfy the rotation equation
almost everywhere, with no smoothness assumed. -/
theorem area_energy_equality_ode_lipschitz (γ : ℝ → ℂ) (K : NNReal)
    (hγ : LipschitzWith K γ) (hclosed : γ 0 = γ 1)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) :
    ∃ c : ℂ, ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt γ ((2 * Real.pi * Complex.I) * (γ t - c)) t := by
  let x := fun t => (γ t).re
  let y := fun t => (γ t).im
  have hxLip := Complex.reCLM.lipschitzWith.comp hγ
  have hyLip := Complex.imCLM.lipschitzWith.comp hγ
  have hx : AbsolutelyContinuousOnInterval x 0 1 := hxLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hy : AbsolutelyContinuousOnInterval y 0 1 := hyLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdx := lipschitz_deriv_memLp_two x _ hxLip
  have hdy := lipschitz_deriv_memLp_two y _ hyLip
  have hxc : x 0 = x 1 := congrArg Complex.re hclosed
  have hyc : y 0 = y 1 := congrArg Complex.im hclosed
  have hdiff : ∀ᵐ t ∂volume, DifferentiableAt ℝ γ t := hγ.ae_differentiableAt
  have hdr (t : ℝ) (ht : DifferentiableAt ℝ γ t) : deriv x t = (deriv γ t).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
  have hdi (t : ℝ) (ht : DifferentiableAt ℝ γ t) : deriv y t = (deriv γ t).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
  have harea : (∫ t in (0 : ℝ)..1, x t * deriv y t) =
      ∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdiff] with t ht _
    rw [hdi t ht]
  have henergy : (∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdiff] with t ht _
    rw [hdr t ht, hdi t ht, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two]
  have he : 4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) =
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2 := by rwa [harea, henergy]
  have hb := area_energy_equality_coordinate_ac x y hx hy hxc hyc hdx hdy he
  have hibp : (∫ t in (0 : ℝ)..1, y t * deriv x t) =
      -(∫ t in (0 : ℝ)..1, x t * deriv y t) := by
    rw [hy.integral_mul_deriv_eq_deriv_mul hx, hyc, hxc, sub_self, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  have hdn (t : ℝ) : deriv (fun s => -y s) t = -deriv y t := deriv.neg
  have he' : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (-y t) * deriv x t) =
      ∫ t in (0 : ℝ)..1, deriv (fun s => -y s) t ^ 2 + deriv x t ^ 2 := by
    simp only [hdn, neg_sq, neg_mul, intervalIntegral.integral_neg, hibp, neg_neg]
    rw [he]
    apply intervalIntegral.integral_congr
    intro t _
    change deriv x t ^ 2 + deriv y t ^ 2 = deriv y t ^ 2 + deriv x t ^ 2
    ring
  have hdneg : MemLp (deriv (fun t => -y t)) 2 (volume.restrict (Ioc 0 1)) := by
    have he : deriv (fun t => -y t) = -deriv y := by
      ext t
      exact hdn t
    rw [he]
    exact hdy.neg
  have ha := area_energy_equality_coordinate_ac (fun t => -y t) x hy.neg hx
    (congrArg Neg.neg hyc) hxc hdneg hdx he'
  refine ⟨⟨∫ t in (0 : ℝ)..1, x t, ∫ t in (0 : ℝ)..1, y t⟩, ?_⟩
  have hdiff' := hdiff.filter_mono (ae_mono (Measure.restrict_le_self (s := Ioc (0 : ℝ) 1)))
  filter_upwards [ha, hb, hdiff'] with t hat hbt hdt
  convert hdt.hasDerivAt using 1
  apply Complex.ext
  · simp only [intervalIntegral.integral_neg] at hat
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      mul_zero, sub_zero, zero_sub, mul_one, add_zero]
    norm_num
    rw [← hdr t hdt]
    linarith
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      mul_zero, sub_zero, zero_sub, mul_one, add_zero, zero_add]
    norm_num
    rw [← hdi t hdt]
    exact hbt.symm


/-- Solve the rotation ODE for a Lipschitz curve even when its equation holds
only almost everywhere. Absolute continuity rules out singular solutions. -/
theorem rotation_ode_solution_lipschitz (γ : ℝ → ℂ) (K : NNReal)
    (hγ : LipschitzWith K γ) (c : ℂ)
    (hode : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt γ ((2 * Real.pi * Complex.I) * (γ t - c)) t) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      γ t = c + Complex.exp ((2 * Real.pi * Complex.I) * t) * (γ 0 - c) := by
  let k : ℂ := 2 * Real.pi * Complex.I
  let F := fun t : ℝ => Complex.exp (-k * t) * (γ t - c)
  have hg : ContDiff ℝ 1 (fun t : ℝ => Complex.exp (-k * t)) :=
    Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
  have hγac : AbsolutelyContinuousOnInterval γ 0 1 :=
    hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hcac : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 1 :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hFac : AbsolutelyContinuousOnInterval F 0 1 := by
    simpa only [smul_eq_mul] using!
      hg.contDiffOn.absolutelyContinuousOnInterval.fun_smul (hγac.fun_sub hcac)
  have hodecc := hode
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hodecc
  have hodeglobal := (ae_restrict_iff' measurableSet_Icc).mp hodecc
  have hFzero : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 1 → HasDerivAt F 0 t := by
    filter_upwards [hodeglobal] with t ht hmem
    have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := t)
    have hd := ((hr.const_mul (-k)).cexp).mul
      ((ht (by simpa using hmem)).sub_const c)
    convert hd using 1
    dsimp only [k]
    ring
  obtain ⟨C, hC⟩ := hFac.const_of_ae_hasDerivAt_zero hFzero
  intro t ht
  have he : F t = F 0 := (hC t (by simpa using ht)).trans
    (hC 0 (by norm_num)).symm
  have hm := congrArg (fun z => Complex.exp (k * t) * z) he
  dsimp only [F] at hm
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hm
  rw [← mul_assoc, ← Complex.exp_add] at hm
  have hc : k * (t : ℂ) + -k * t = 0 := by ring
  rw [hc, Complex.exp_zero, one_mul] at hm
  dsimp only [k] at hm
  linear_combination hm

/-- Lipschitz area-energy equality forces the whole simple closed curve to be
exactly a circle, with no smoothness assumption. -/
theorem area_energy_equality_circle_lipschitz (γ : ℝ → ℂ) (K : NNReal)
    (hγ : LipschitzWith K γ) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico (0 : ℝ) 1))
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc 0 1 = Metric.sphere c r := by
  obtain ⟨c, hc⟩ := area_energy_equality_ode_lipschitz γ K hγ hclosed heq
  have hparam := rotation_ode_solution_lipschitz γ K hγ c hc
  have hv : γ 0 - c ≠ 0 := by
    intro hz
    have he : γ (1 / 2) = γ 0 := by
      rw [hparam (1 / 2) (by norm_num), hz, mul_zero, add_zero]
      exact (sub_eq_zero.mp hz).symm
    have hb := hsimple (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)
      (by norm_num : (0 : ℝ) ∈ Ico 0 1) he
    norm_num at hb
  refine ⟨c, ‖γ 0 - c‖, norm_pos_iff.mpr hv, ?_⟩
  exact circle_image_of_clock γ id c (by simp) hparam hv

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.area_energy_defect_bound_ac
#check_upstream ClassicalTheorems.Progress.Isoperimetric.area_energy_equality_ode_lipschitz
#check_upstream ClassicalTheorems.Progress.Isoperimetric.area_energy_equality_circle_lipschitz

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricDefect
import Mathlib.Topology.Order.Compact

/-! Equality defects in the original parameter, allowing zero speed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ClassicalTheorems.Progress.Isoperimetric

def curveLength (γ : ℝ → ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ‖deriv γ t‖

def weightedCoordMean (γ : ℝ → ℂ) (ε : ℝ) : ℝ :=
  ((∫ t in (0 : ℝ)..1, (γ t).re * ‖deriv γ t‖) +
    ε * (∫ t in (0 : ℝ)..1, (γ t).re)) /
      max (curveLength γ / 2) (curveLength γ + ε)

def speedDefect (γ : ℝ → ℂ) (ε t : ℝ) : ℝ :=
  2 * Real.pi * (‖deriv γ t‖ + ε) * ((γ t).re - weightedCoordMean γ ε) -
    (curveLength γ + ε) * (deriv γ t).im

theorem weightedCoordMean_density (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (ε : ℝ) (hε : 0 < ε) (hL : 0 < curveLength γ) :
    weightedCoordMean γ ε =
      (∫ t in (0 : ℝ)..1, (γ t).re * (‖deriv γ t‖ + ε)) / (curveLength γ + ε) := by
  have hmax : max (curveLength γ / 2) (curveLength γ + ε) = curveLength γ + ε :=
    max_eq_right (by linarith)
  unfold weightedCoordMean
  rw [hmax]
  congr 1
  have hi : IntervalIntegrable (fun t => (γ t).re * ‖deriv γ t‖) volume 0 1 :=
    ((Complex.continuous_re.comp hγ.continuous).mul hγ.continuous_deriv_one.norm).intervalIntegrable 0 1
  have hi' : IntervalIntegrable (fun t => ε * (γ t).re) volume 0 1 :=
    ((Complex.continuous_re.comp hγ.continuous).intervalIntegrable 0 1).const_mul ε
  calc
    _ = ∫ t in (0 : ℝ)..1, (γ t).re * ‖deriv γ t‖ + ε * (γ t).re := by
      rw [intervalIntegral.integral_add hi hi', intervalIntegral.integral_const_mul]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      ring

/-- A quantitative estimate for the defect, measured in the original parameter. -/
theorem speedDefect_estimate (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hL : 0 < curveLength γ)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) = curveLength γ ^ 2)
    (M : ℝ) (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    (∫ t in (0 : ℝ)..1, speedDefect γ ε t ^ 2) ≤
      (curveLength γ + ε) * (M + ε) * ((curveLength γ + ε) ^ 2 - curveLength γ ^ 2) := by
  let w := fun t => ‖deriv γ t‖ + ε
  let L := curveLength γ + ε
  have hLp : 0 < L := by dsimp only [L]; positivity
  have hw : Continuous w := hγ.continuous_deriv_one.norm.add continuous_const
  have hwp (t : ℝ) : 0 < w t := by dsimp only [w]; positivity
  obtain ⟨φ, hφ, hmono, hφ0, hφ1, hdφ'⟩ := positive_density_reparametrization w hw ε hε
    (fun t => by dsimp only [w]; exact le_add_of_nonneg_left (norm_nonneg _))
  have hLid : (∫ t in (0 : ℝ)..1, w t) = L := by
    rw [intervalIntegral.integral_add (hγ.continuous_deriv_one.norm.intervalIntegrable 0 1)
      intervalIntegrable_const]
    simp [curveLength, L]
  have hdφ (t : ℝ) : HasDerivAt φ (L / w (φ t)) t := by simpa only [hLid] using hdφ' t
  have hφmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : φ t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hφ0] using hmono.monotone ht.1
    · simpa only [hφ1] using hmono.monotone ht.2
  let δ := γ ∘ φ
  have hδ : ContDiff ℝ 1 δ := hγ.comp hφ
  have hcδ : δ 0 = δ 1 := by simpa [δ, hφ0, hφ1] using hclosed
  have hdδ (t : ℝ) : deriv δ t = (L / w (φ t)) • deriv γ (φ t) := by
    rw [deriv_reparam γ hγ φ hφ, (hdφ t).deriv]
  have hnδ (t : ℝ) : ‖deriv δ t‖ ≤ L := by
    rw [hdδ, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hLp (hwp _)),
      div_mul_eq_mul_div, div_le_iff₀ (hwp _)]
    dsimp only [w]
    nlinarith
  have hmean : (∫ t in (0 : ℝ)..1, (δ t).re) = weightedCoordMean γ ε := by
    rw [weightedCoordMean_density γ hγ ε hε hL]
    exact density_reparam_mean (fun t => (γ t).re) w φ
      (Complex.continuous_re.comp hγ.continuous) hw hφ hφ0 hφ1 L hLp.ne' hwp hdφ
  let d := fun t => 2 * Real.pi * ((δ t).re - ∫ s in (0 : ℝ)..1, (δ s).re) - (deriv δ t).im
  have hdcont : Continuous d :=
    (continuous_const.mul ((Complex.continuous_re.comp hδ.continuous).sub continuous_const)).sub
      (Complex.continuous_im.comp hδ.continuous_deriv_one)
  have hpoint (t : ℝ) : speedDefect γ ε (φ t) = w (φ t) * d t := by
    dsimp only [speedDefect, d]
    rw [hmean, hdδ, Complex.smul_im, smul_eq_mul]
    change 2 * Real.pi * w (φ t) * ((γ (φ t)).re - weightedCoordMean γ ε) -
      L * (deriv γ (φ t)).im = w (φ t) *
        (2 * Real.pi * ((γ (φ t)).re - weightedCoordMean γ ε) -
          (L / w (φ t)) * (deriv γ (φ t)).im)
    field_simp [(hwp (φ t)).ne']
  have henergy : (∫ t in (0 : ℝ)..1, (deriv δ t).re ^ 2 + (deriv δ t).im ^ 2) ≤ L ^ 2 := by
    have hi : IntervalIntegrable (fun t => (deriv δ t).re ^ 2 + (deriv δ t).im ^ 2) volume 0 1 :=
      (((Complex.continuous_re.comp hδ.continuous_deriv_one).pow 2).add
        ((Complex.continuous_im.comp hδ.continuous_deriv_one).pow 2)).intervalIntegrable 0 1
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, L ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi intervalIntegrable_const
        intro t _
        have hn : (deriv δ t).re ^ 2 + (deriv δ t).im ^ 2 = ‖deriv δ t‖ ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq]
          simp only [Complex.normSq_apply, pow_two]
        rw [hn]
        exact pow_le_pow_left₀ (norm_nonneg _) (hnδ t) 2
      _ = L ^ 2 := by simp
  have hdef : (∫ t in (0 : ℝ)..1, d t ^ 2) ≤ L ^ 2 - curveLength γ ^ 2 := by
    have h := area_energy_defect_bound (fun t => (δ t).re) (fun t => (δ t).im)
      (Complex.reCLM.contDiff.comp hδ) (Complex.imCLM.contDiff.comp hδ)
      (congrArg Complex.re hcδ) (congrArg Complex.im hcδ)
    simp only [Green.deriv_re δ hδ, Green.deriv_im δ hδ] at h
    change (∫ t in (0 : ℝ)..1, d t ^ 2) ≤
      (∫ t in (0 : ℝ)..1, (deriv δ t).re ^ 2 + (deriv δ t).im ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ (φ t)).re * (deriv (γ ∘ φ) t).im) at h
    rw [reparam_signed_area γ hγ φ hφ hφ0 hφ1, heq] at h
    linarith
  have hF : Continuous (speedDefect γ ε) :=
    ((continuous_const.mul (hγ.continuous_deriv_one.norm.add continuous_const)).mul
      ((Complex.continuous_re.comp hγ.continuous).sub continuous_const)).sub
        (continuous_const.mul (Complex.continuous_im.comp hγ.continuous_deriv_one))
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1)
    (g := fun t => speedDefect γ ε t ^ 2) (fun t _ => hdφ t)
    (hφ.continuous_deriv_one.continuousOn.congr (fun t _ => (hdφ t).deriv.symm)) (hF.pow 2)
  rw [hφ0, hφ1] at hsub
  have hMn : 0 ≤ M := (norm_nonneg (deriv γ 0)).trans (hM 0 (by norm_num))
  have hC : 0 ≤ L * (M + ε) := by positivity
  calc
    _ = ∫ t in (0 : ℝ)..1, L * w (φ t) * d t ^ 2 := by
      rw [← hsub]
      apply intervalIntegral.integral_congr
      intro t _
      change speedDefect γ ε (φ t) ^ 2 * (L / w (φ t)) = L * w (φ t) * d t ^ 2
      rw [hpoint]
      field_simp [(hwp (φ t)).ne']
    _ ≤ L * (M + ε) * ∫ t in (0 : ℝ)..1, d t ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      have hi : IntervalIntegrable (fun t => L * w (φ t) * d t ^ 2) volume 0 1 :=
        ((continuous_const.mul (hw.comp hφ.continuous)).mul (hdcont.pow 2)).intervalIntegrable 0 1
      apply intervalIntegral.integral_mono_on (by norm_num) hi
        (((hdcont.pow 2).intervalIntegrable 0 1).const_mul (L * (M + ε)))
      intro t ht
      change L * w (φ t) * d t ^ 2 ≤ L * (M + ε) * d t ^ 2
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ hLp.le
      exact add_le_add (hM (φ t) (hφmem t ht)) le_rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left hdef hC

theorem weightedCoordMean_continuous (γ : ℝ → ℂ) (hL : 0 < curveLength γ) :
    Continuous (weightedCoordMean γ) := by
  have hd : Continuous (fun ε : ℝ => max (curveLength γ / 2) (curveLength γ + ε)) :=
    continuous_const.max (continuous_const.add continuous_id)
  apply (continuous_const.add (continuous_id.mul continuous_const)).div hd
  intro ε
  exact ne_of_gt (lt_of_lt_of_le (by positivity : 0 < curveLength γ / 2) (le_max_left _ _))

theorem speedDefect_continuous (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hL : 0 < curveLength γ) :
    Continuous (Function.uncurry (speedDefect γ)) := by
  have hs : Continuous (fun p : ℝ × ℝ => ‖deriv γ p.2‖ + p.1) :=
    (hγ.continuous_deriv_one.norm.comp continuous_snd).add continuous_fst
  have hx : Continuous (fun p : ℝ × ℝ => (γ p.2).re - weightedCoordMean γ p.1) :=
    ((Complex.continuous_re.comp hγ.continuous).comp continuous_snd).sub
      ((weightedCoordMean_continuous γ hL).comp continuous_fst)
  exact ((continuous_const.mul hs).mul hx).sub
    ((continuous_const.add continuous_fst).mul
      ((Complex.continuous_im.comp hγ.continuous_deriv_one).comp continuous_snd))

/-- Equality forces the speed-weighted coordinate defect to vanish, even where
the original parametrization has zero derivative. -/
theorem speedDefect_zero (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hL : 0 < curveLength γ)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) = curveLength γ ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) 1, speedDefect γ 0 t = 0 := by
  have hs := hγ.continuous_deriv_one.norm
  obtain ⟨M, hM⟩ := (isCompact_Icc.bddAbove_image hs.continuousOn)
  have hMb : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ M := fun t ht => hM ⟨t, ht, rfl⟩
  have hc : Continuous (fun ε : ℝ => ∫ t in Icc (0 : ℝ) 1, speedDefect γ ε t ^ 2) :=
    continuous_parametric_integral_of_continuous ((speedDefect_continuous γ hγ hL).pow 2) isCompact_Icc
  have hi : Continuous (fun ε : ℝ => ∫ t in (0 : ℝ)..1, speedDefect γ ε t ^ 2) := by
    convert hc using 1
    ext ε
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Icc_eq_integral_Ioc]
  have hR : Continuous (fun ε : ℝ => (curveLength γ + ε) * (M + ε) *
      ((curveLength γ + ε) ^ 2 - curveLength γ ^ 2)) := by fun_prop
  have hlimI := (hi.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlimR := (hR.continuousAt (x := (0 : ℝ))).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hzero : (∫ t in (0 : ℝ)..1, speedDefect γ 0 t ^ 2) ≤ 0 := by
    have h := le_of_tendsto_of_tendsto hlimI hlimR (show
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t in (0 : ℝ)..1, speedDefect γ ε t ^ 2) ≤
        (curveLength γ + ε) * (M + ε) * ((curveLength γ + ε) ^ 2 - curveLength γ ^ 2) from by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact speedDefect_estimate γ hγ hclosed hL heq M hMb ε hε)
    simpa using h
  exact continuous_sq_zero_of_integral_le_zero _
    ((speedDefect_continuous γ hγ hL).comp (continuous_const.prodMk continuous_id)) hzero

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.speedDefect_estimate
#check_upstream ClassicalTheorems.Progress.Isoperimetric.speedDefect_zero

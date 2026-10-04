/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenShear

/-! Green's theorem for a positively oriented C¹ Jordan boundary.
The compact-support extension and small-shear reduction discharge the arbitrary-field case. -/
noncomputable section
open MeasureTheory Set Function
namespace ClassicalTheorems.Progress.Green

theorem greens_theorem_without_regularity (D U : Set ℂ) (γ : ℝ → ℂ) (P Q : ℂ → ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨R, W, K, hR, _, hRLip, hRBound, hW, hDW, hRP, hdRP⟩ :=
    exists_lipschitz_extension (closure D) U hBounded.isCompact_closure hOpen hNeighborhood P hP
  obtain ⟨S, V, L, hS, _, hSLip, hSBound, hV, hDV, hSQ, hdSQ⟩ :=
    exists_lipschitz_extension (closure D) U hBounded.isCompact_closure hOpen hNeighborhood Q hQ
  have hγW := curve_mapsTo_neighborhood D W γ hBoundary hDW
  have hγV := curve_mapsTo_neighborhood D V γ hBoundary hDV
  have hRPline : (∫ t in (0 : ℝ)..1, R (γ t) * (deriv γ t).re) =
      ∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re := by
    apply intervalIntegral.integral_congr
    intro t ht
    change R (γ t) * (deriv γ t).re = P (γ t) * (deriv γ t).re
    rw [hRP (hγW (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))]
  have hSQline : (∫ t in (0 : ℝ)..1, S (γ t) * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, Q (γ t) * (deriv γ t).im := by
    apply intervalIntegral.integral_congr
    intro t ht
    change S (γ t) * (deriv γ t).im = Q (γ t) * (deriv γ t).im
    rw [hSQ (hγV (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht))]
  have hRParea : (∫ z in D, fderiv ℝ R z Complex.I) = ∫ z in D, fderiv ℝ P z Complex.I := by
    apply setIntegral_congr_fun hDomain.measurableSet
    intro z hz
    change fderiv ℝ R z Complex.I = fderiv ℝ P z Complex.I
    rw [hdRP (hDW (subset_closure hz))]
  have hSQarea : (∫ z in D, fderiv ℝ S z (1 : ℂ)) = ∫ z in D, fderiv ℝ Q z (1 : ℂ) := by
    apply setIntegral_congr_fun hDomain.measurableSet
    intro z hz
    change fderiv ℝ S z (1 : ℂ) = fderiv ℝ Q z (1 : ℂ)
    rw [hdSQ (hDV (subset_closure hz))]
  have hDirP := greens_directional D γ hDomain hBounded hConnected hBoundary
    hCurve hClosed hSimple hPositive R hR K hRLip hRBound Complex.I
  have hDirQ := greens_directional D γ hDomain hBounded hConnected hBoundary
    hCurve hClosed hSimple hPositive S hS L hSLip hSBound (1 : ℂ)
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hDirP
  simp only [Complex.one_re, Complex.one_im, zero_mul, one_mul, sub_zero] at hDirQ
  rw [hRPline, hRParea] at hDirP
  rw [hSQline, hSQarea] at hDirQ
  have hγU := curve_mapsTo_neighborhood D U γ hBoundary hNeighborhood
  have hd := hCurve.continuous_deriv_one
  have hpc := hP.continuousOn.comp hCurve.continuous.continuousOn hγU
  have hqc := hQ.continuousOn.comp hCurve.continuous.continuousOn hγU
  have hiP : IntervalIntegrable (fun t => P (γ t) * (deriv γ t).re) volume 0 1 := (hpc.mul (Complex.continuous_re.comp hd).continuousOn).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have hiQ : IntervalIntegrable (fun t => Q (γ t) * (deriv γ t).im) volume 0 1 := (hqc.mul (Complex.continuous_im.comp hd).continuousOn).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have hcP := (hP.continuousOn_fderiv_of_isOpen hOpen le_rfl).clm_apply
    (continuousOn_const (s := U) (c := Complex.I))
  have hcQ := (hQ.continuousOn_fderiv_of_isOpen hOpen le_rfl).clm_apply
    (continuousOn_const (s := U) (c := (1 : ℂ)))
  have haP : IntegrableOn (fun z => fderiv ℝ P z Complex.I) D :=
    ((hcP.mono hNeighborhood).integrableOn_compact hBounded.isCompact_closure).mono_set subset_closure
  have haQ : IntegrableOn (fun z => fderiv ℝ Q z (1 : ℂ)) D :=
    ((hcQ.mono hNeighborhood).integrableOn_compact hBounded.isCompact_closure).mono_set subset_closure
  rw [intervalIntegral.integral_add hiP hiQ, integral_sub haQ haP]
  linarith

/-- Green identity for a regular, positively oriented boundary. -/
theorem greens_theorem (D U : Set ℂ) (γ : ℝ → ℂ) (P Q : ℂ → ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (_hRegular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I :=
  greens_theorem_without_regularity D U γ P Q hDomain hBounded hConnected
    hBoundary hOpen hNeighborhood hCurve hClosed hSimple hPositive hP hQ

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_without_regularity

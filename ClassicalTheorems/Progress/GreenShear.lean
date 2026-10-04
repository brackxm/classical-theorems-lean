/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenClassicalArea
import ClassicalTheorems.Progress.GreenShearGeometry
import ClassicalTheorems.Progress.GreenExtension
import Mathlib.MeasureTheory.Function.Jacobian

/-! Assembly of the small-shear reduction for Green’s theorem. -/
noncomputable section
open MeasureTheory Set Function MovingSofa
open scoped NNReal
namespace ClassicalTheorems.Progress.Green

/-- The area identity survives a globally C¹ perturbation of the identity with
Lipschitz constant below one, on the image of the same domain. -/
theorem area_perturb_of_lipschitz (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1) (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (g : ℂ → ℂ) (K : ℝ≥0) (hg : LipschitzWith K g) (hK : K < 1)
    (hSmooth : ContDiff ℝ 1 g) :
    (∫ t in (0 : ℝ)..1, (γ t + g (γ t)).re *
      (deriv (fun s => γ s + g (γ s)) t).im) =
      (volume ((fun z => z + g z) '' D)).toReal := by
  let T : ℂ → ℂ := fun z => z + g z
  let η : ℝ → ℂ := fun t => T (γ t)
  obtain ⟨e, he⟩ := exists_homeomorph_add_of_lipschitz g K hg hK
  have heq : (e : ℂ → ℂ) = T := funext he
  have hTinj : Injective T := heq ▸ e.injective
  have hη : ContDiff ℝ 1 η := hCurve.add (hSmooth.comp hCurve)
  have hηClosed : η 0 = η 1 := congrArg T hClosed
  have hηSimple : InjOn η (Ico 0 1) := hTinj.comp_injOn hSimple
  have hTDopen : IsOpen (T '' D) := heq ▸ e.isOpenMap D hDomain
  have hTDbdd : Bornology.IsBounded (T '' D) :=
    (LipschitzWith.id.add hg).isBounded_image hBounded
  have hTDconn : IsConnected (T '' D) :=
    hConnected.image T (continuous_id.add hg.continuous).continuousOn
  have hTDfront : frontier (T '' D) = η '' Icc 0 1 := by
    calc
      _ = T '' frontier D := heq ▸ (e.image_frontier D).symm
      _ = _ := by rw [hBoundary, image_image]
  have hηPositive : ∀ z ∈ T '' D,
      (∫ t in (0 : ℝ)..1, (deriv η t / (η t - z)).im) = 2 * Real.pi := by
    rintro _ ⟨z, hz, rfl⟩
    have hzγ : z ∉ γ '' Icc 0 1 := by
      rw [← hBoundary]
      exact fun hzf => (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hDomain)) hzf hz
    have hzη : T z ∉ η '' Icc 0 1 := by
      rintro ⟨t, ht, heqt⟩
      exact hzγ ⟨t, ht, hTinj heqt⟩
    have hwγ := complex_curveWinding_integral γ hCurve hClosed hSimple z hzγ
    have hwη := complex_curveWinding_integral η hη hηClosed hηSimple (T z) hzη
    have hwind := complex_winding_add_of_lipschitz γ g K hCurve.continuous hClosed hg hK z hzγ
    calc
      _ = 2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
          (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (η t))
          (Complex.orthonormalBasisOneI.repr (T z)) := hwη.symm
      _ = 2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
          (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (γ t))
          (Complex.orthonormalBasisOneI.repr z) := congrArg (fun w => 2 * Real.pi * w) hwind
      _ = _ := hwγ
      _ = _ := hPositive z hz
  exact complex_signedArea_eq_domain_area (T '' D) η hTDopen hTDbdd hTDconn hTDfront
    hη hηClosed hηSimple hηPositive


/-- The determinant of a rank-one perturbation of the plane identity. -/
theorem rankOne_det (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ((ContinuousLinearMap.id ℝ ℂ) + L.smulRight v).toLinearMap.det = 1 + L v := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, one_form_coordinates L v]
  ring

/-- The change in the area of a sheared domain is the integral of its rank-one Jacobian. -/
theorem shear_area_change (D : Set ℂ) (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D)
    (P : ℂ → ℝ) (hP : ContDiff ℝ 1 P) (K : ℝ≥0)
    (hDeriv : ∀ z, ‖fderiv ℝ P z‖ ≤ K) (v : ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (hSmall : ε * ((K : ℝ) * ‖v‖) < 1)
    (hInj : InjOn (fun z => z + (ε * P z) • v) D) :
    (volume ((fun z => z + (ε * P z) • v) '' D)).toReal =
      (volume D).toReal + ε * ∫ z in D, fderiv ℝ P z v := by
  let T : ℂ → ℂ := fun z => z + (ε * P z) • v
  let T' : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    (ContinuousLinearMap.id ℝ ℂ) + (ε • fderiv ℝ P z).smulRight v
  have hd (z : ℂ) : HasFDerivAt T (T' z) z := by
    have hs := (hasFDerivAt_id z).add
      (((hP.differentiable one_ne_zero z).hasFDerivAt.const_smul ε).smul_const v)
    change HasFDerivAt T (T' z) z at hs
    exact hs
  have hdet (z : ℂ) : (T' z).det = 1 + ε * fderiv ℝ P z v := by
    simpa only [T', ContinuousLinearMap.det, smul_apply, smul_eq_mul]
      using rankOne_det (ε • fderiv ℝ P z) v
  have hpos (z : ℂ) : 0 < 1 + ε * fderiv ℝ P z v := by
    have hNorm : |fderiv ℝ P z v| ≤ (K : ℝ) * ‖v‖ := by
      calc
        _ = ‖fderiv ℝ P z v‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ P z‖ * ‖v‖ := (fderiv ℝ P z).le_opNorm v
        _ ≤ _ := mul_le_mul_of_nonneg_right (hDeriv z) (norm_nonneg v)
    have hLower := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hNorm) hε
    nlinarith
  have hArea := integral_image_eq_integral_abs_det_fderiv_smul volume
    hDomain.measurableSet (fun z _ => (hd z).hasFDerivWithinAt) hInj (fun _ => (1 : ℝ))
  have hCurl : IntegrableOn (fun z => fderiv ℝ P z v) D :=
    (((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn.integrableOn_compact hBounded.isCompact_closure).mono_set subset_closure
  have hOne : IntegrableOn (fun _ : ℂ => (1 : ℝ)) D :=
    (continuous_const.continuousOn.integrableOn_compact hBounded.isCompact_closure).mono_set subset_closure
  calc
    _ = ∫ z in D, 1 + ε * fderiv ℝ P z v := by
      calc
        _ = ∫ z in T '' D, (1 : ℝ) := by simp [T, measureReal_def]
        _ = ∫ z in D, |(T' z).det| • (1 : ℝ) := hArea
        _ = _ := by
          apply setIntegral_congr_fun hDomain.measurableSet
          intro z _
          change |(T' z).det| * (1 : ℝ) = 1 + ε * fderiv ℝ P z v
          rw [hdet, abs_of_pos (hpos z)]
          simp
    _ = _ := by
      rw [integral_add hOne (hCurl.const_mul ε), integral_const_mul, setIntegral_const]
      simp [measureReal_def]

theorem scalar_perturb_lipschitz (P : ℂ → ℝ) (K : ℝ≥0) (hP : LipschitzWith K P) (v : ℂ) (ε : ℝ) (hε : 0 ≤ ε) :
    LipschitzWith ⟨ε * (K : ℝ) * ‖v‖, mul_nonneg (mul_nonneg hε K.coe_nonneg) (norm_nonneg _)⟩
      (fun z => (ε * P z) • v) := by
  apply LipschitzWith.of_dist_le_mul
  intro z p
  have hLip := hP.dist_le_mul z p
  simp only [dist_eq_norm] at hLip ⊢
  calc
    _ = ε * ‖P z - P p‖ * ‖v‖ := by
      rw [← sub_smul, ← mul_sub, norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hε]
      rw [Real.norm_eq_abs]
    _ ≤ ε * ((K : ℝ) * ‖z - p‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLip hε) (norm_nonneg v)
    _ = _ := by
      change ε * ((K : ℝ) * ‖z - p‖) * ‖v‖ =
        (ε * (K : ℝ) * ‖v‖) * ‖z - p‖
      ring

/-- The directional Green identity for a globally C¹ Lipschitz field with bounded derivative.
It follows by comparing the boundary and Jacobian area changes of a small shear. -/
theorem greens_directional (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1) (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (P : ℂ → ℝ) (hP : ContDiff ℝ 1 P) (K : ℝ≥0)
    (hLip : LipschitzWith K P) (hDeriv : ∀ z, ‖fderiv ℝ P z‖ ≤ K) (v : ℂ) :
    v.re * (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).im) -
      v.im * (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re) =
      ∫ z in D, fderiv ℝ P z v := by
  let ε : ℝ := (2 * ((K : ℝ) * ‖v‖ + 1))⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ha : 0 ≤ (K : ℝ) * ‖v‖ := mul_nonneg K.coe_nonneg (norm_nonneg v)
  have hSmall : ε * ((K : ℝ) * ‖v‖) < 1 := by
    dsimp [ε]
    rw [inv_mul_eq_div]
    apply (div_lt_one (by positivity)).2
    linarith
  let C : ℝ≥0 := ⟨ε * (K : ℝ) * ‖v‖,
    mul_nonneg (mul_nonneg hε.le K.coe_nonneg) (norm_nonneg v)⟩
  let g : ℂ → ℂ := fun z => (ε * P z) • v
  let T : ℂ → ℂ := fun z => z + g z
  let η : ℝ → ℂ := fun t => T (γ t)
  have hg : LipschitzWith C g := scalar_perturb_lipschitz P K hLip v ε hε.le
  have hC : C < 1 := by change ε * (K : ℝ) * ‖v‖ < 1; simpa only [mul_assoc] using hSmall
  have hgSmooth : ContDiff ℝ 1 g := (contDiff_const.mul hP).smul_const v
  have hη : ContDiff ℝ 1 η := hCurve.add (hgSmooth.comp hCurve)
  obtain ⟨e, he⟩ := exists_homeomorph_add_of_lipschitz g C hg hC
  have heq : (e : ℂ → ℂ) = T := funext he
  have hTinj : Injective T := heq ▸ e.injective
  have hAreaT := area_perturb_of_lipschitz D γ hDomain hBounded hConnected hBoundary
    hCurve hClosed hSimple hPositive g C hg hC hgSmooth
  have hAreaJ := shear_area_change D hDomain hBounded P hP K hDeriv v ε hε.le hSmall
    hTinj.injOn
  let x : ℝ → ℝ := fun t => (γ t).re
  let y : ℝ → ℝ := fun t => (γ t).im
  let f : ℝ → ℝ := P ∘ γ
  have hx : ContDiff ℝ 1 x := Complex.reCLM.contDiff.comp hCurve
  have hy : ContDiff ℝ 1 y := Complex.imCLM.contDiff.comp hCurve
  have hf : ContDiff ℝ 1 f := hP.comp hCurve
  have hxc : x 0 = x 1 := congrArg Complex.re hClosed
  have hfc : f 0 = f 1 := congrArg P hClosed
  have hRe : (fun t => (η t).re) = (fun t => x t + (ε * v.re) * f t) := by
    funext t
    simp only [η, T, g, x, f, Function.comp_apply, Complex.add_re, Complex.smul_re, smul_eq_mul]
    ring
  have hIm : (fun t => (η t).im) = (fun t => y t + (ε * v.im) * f t) := by
    funext t
    simp only [η, T, g, y, f, Function.comp_apply, Complex.add_im, Complex.smul_im, smul_eq_mul]
    ring
  have hNew : signedArea (fun t => (η t).re) (fun t => (η t).im) =
      (volume (T '' D)).toReal := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (η t).re * (deriv η t).im := by
        unfold signedArea
        apply intervalIntegral.integral_congr
        intro t _
        change (η t).re * deriv (fun s => (η s).im) t = _
        rw [deriv_im η hη t]
      _ = _ := hAreaT
  have hOld : signedArea x y = (volume D).toReal := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im := by
        unfold signedArea
        apply intervalIntegral.integral_congr
        intro t _
        change (γ t).re * deriv (fun s => (γ s).im) t = _
        rw [deriv_im γ hCurve t]
      _ = _ := complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected hBoundary
        hCurve hClosed hSimple hPositive
  have hIx : (∫ t in (0 : ℝ)..1, f t * deriv x t) =
      ∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re := by
    apply intervalIntegral.integral_congr
    intro t _
    change P (γ t) * deriv (fun s => (γ s).re) t = _
    rw [deriv_re γ hCurve t]
  have hIy : (∫ t in (0 : ℝ)..1, f t * deriv y t) =
      ∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).im := by
    apply intervalIntegral.integral_congr
    intro t _
    change P (γ t) * deriv (fun s => (γ s).im) t = _
    rw [deriv_im γ hCurve t]
  have hVariation := signedArea_perturb x y f (ε * v.re) (ε * v.im) hx hy hf hxc hfc
  rw [← hRe, ← hIm, hNew, hOld, hIx, hIy, hAreaJ] at hVariation
  apply mul_left_cancel₀ (ne_of_gt hε)
  nlinarith [hVariation]

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.area_perturb_of_lipschitz

#check_upstream ClassicalTheorems.Progress.Green.rankOne_det
#check_upstream ClassicalTheorems.Progress.Green.shear_area_change

#check_upstream ClassicalTheorems.Progress.Green.scalar_perturb_lipschitz

#check_upstream ClassicalTheorems.Progress.Green.greens_directional

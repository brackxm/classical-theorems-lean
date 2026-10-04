/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Verified supporting calculus for Green’s theorem. The full Jordan-domain identity is proved
in `ClassicalTheorems.Progress.GreenFull` and indexed by `ClassicalTheorems.Green`. -/

namespace ClassicalTheorems.Progress.Green
open MeasureTheory Set

/-- The boundary and neighbourhood hypotheses put the entire curve in `U`. -/
theorem curve_mapsTo_neighborhood (D U : Set ℂ) (γ : ℝ → ℂ)
    (hBoundary : frontier D = γ '' Icc 0 1) (hNeighborhood : closure D ⊆ U) :
    MapsTo γ (Icc 0 1) U := by
  intro t ht
  apply hNeighborhood
  apply frontier_subset_closure
  rw [hBoundary]
  exact ⟨t, ht, rfl⟩

/-- Under the original C¹ assumptions the boundary integral is a genuine
integrable function, rather than a totalized Bochner integral. -/
theorem line_integrable (U : Set ℂ) (γ : ℝ → ℂ) (P Q : ℂ → ℝ)
    (hCurve : ContDiff ℝ 1 γ) (hImage : MapsTo γ (Icc 0 1) U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntervalIntegrable
      (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im)
      volume 0 1 := by
  have hpc := hP.continuousOn.comp hCurve.continuous.continuousOn hImage
  have hqc := hQ.continuousOn.comp hCurve.continuous.continuousOn hImage
  have hd := hCurve.continuous_deriv_one
  exact ((hpc.mul (Complex.continuous_re.comp hd).continuousOn).add
    (hqc.mul (Complex.continuous_im.comp hd).continuousOn)).intervalIntegrable_of_Icc
      (by norm_num)

/-- Compactness of the closure and C¹ regularity give area integrability of
exactly the curl used in the public formulation. -/
theorem curl_integrable (D U : Set ℂ) (P Q : ℂ → ℝ)
    (hBounded : Bornology.IsBounded D) (hOpen : IsOpen U)
    (hNeighborhood : closure D ⊆ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntegrableOn (fun z => fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I) D := by
  have hpc := (hP.continuousOn_fderiv_of_isOpen hOpen le_rfl).clm_apply
    (continuousOn_const (s := U) (c := Complex.I))
  have hqc := (hQ.continuousOn_fderiv_of_isOpen hOpen le_rfl).clm_apply
    (continuousOn_const (s := U) (c := (1 : ℂ)))
  exact (((hqc.sub hpc).mono hNeighborhood).integrableOn_compact
    hBounded.isCompact_closure).mono_set subset_closure

/-- A real linear one-form on the complex plane is determined by its values
on the coordinate basis `1, I`. -/
theorem one_form_coordinates (L : ℂ →L[ℝ] ℝ) (v : ℂ) :
    L v = L 1 * v.re + L Complex.I * v.im := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    L v = L (v.re • (1 : ℂ) + v.im • Complex.I) := congrArg L hv
    _ = L 1 * v.re + L Complex.I * v.im := by
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring

/-- The exact one-form case: integrating the differential of a C¹ potential
around a closed C¹ curve gives zero, with the same component convention as Green’s theorem. -/
theorem exact_closed_curve (γ : ℝ → ℂ) (F : ℂ → ℝ)
    (hCurve : ContDiff ℝ 1 γ) (hF : ContDiff ℝ 1 F) (hClosed : γ 0 = γ 1) :
    (∫ t in (0 : ℝ)..1,
      fderiv ℝ F (γ t) 1 * (deriv γ t).re +
      fderiv ℝ F (γ t) Complex.I * (deriv γ t).im) = 0 := by
  have hc : Continuous (fun t => fderiv ℝ F (γ t) (deriv γ t)) :=
    ((hF.continuous_fderiv one_ne_zero).comp hCurve.continuous).clm_apply
      hCurve.continuous_deriv_one
  have hd (t : ℝ) : HasDerivAt (F ∘ γ) (fderiv ℝ F (γ t) (deriv γ t)) t :=
    ((hF.differentiable one_ne_zero (γ t)).hasFDerivAt).comp_hasDerivAt t
      ((hCurve.differentiable one_ne_zero t).hasDerivAt)
  simp_rw [← one_form_coordinates]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (hc.intervalIntegrable (μ := volume) 0 1)]
  simp [hClosed]

/-- Green's formula on rectangles, with the usual counterclockwise edge signs.
This is the local integration identity used alongside the Jordan-area/shear proof. -/
theorem rectangle (P Q : ℝ × ℝ → ℝ) (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (a b c d : ℝ) :
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y)) -
      (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y)) =
    ∫ x in a..b, ∫ y in c..d,
      fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1) := by
  have hc : Continuous (fun z => fderiv ℝ Q z (1, 0) - fderiv ℝ P z (0, 1)) :=
    ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const).sub
      ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hi : IntegrableOn (fun z => fderiv ℝ Q z (1, 0) - fderiv ℝ P z (0, 1))
      (uIcc a b ×ˢ uIcc c d) :=
    hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)
  have h := integral2_divergence_prod_of_hasFDerivAt Q (-P)
    (fderiv ℝ Q) (fun z => -(fderiv ℝ P z)) a c b d
    hQ.continuous.continuousOn hP.continuous.neg.continuousOn
    (fun z _ => (hQ.differentiable one_ne_zero z).hasFDerivAt)
    (fun z _ => (hP.differentiable one_ne_zero z).hasFDerivAt.neg)
    (by simpa only [neg_apply, sub_eq_add_neg] using hi)
  simp only [neg_apply, Pi.neg_apply,
    ← sub_eq_add_neg, intervalIntegral.integral_neg] at h
  linarith

/-- The signed-area line functional, before identifying it with enclosed area. -/
noncomputable def signedArea (x y : ℝ → ℝ) : ℝ := ∫ t in (0 : ℝ)..1, x t * deriv y t

/-- A vertical shear changes signed area by minus the horizontal line integral.
This is the calculus part of a reduction of general Green to the Jordan area formula. -/
theorem vertical_shear (x y f : ℝ → ℝ) (ε : ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hf : ContDiff ℝ 1 f)
    (hxClosed : x 0 = x 1) (hfClosed : f 0 = f 1) :
    signedArea x (fun t => y t + ε * f t) =
      signedArea x y - ε * ∫ t in (0 : ℝ)..1, f t * deriv x t := by
  have hd (t : ℝ) : deriv (fun s => y s + ε * f s) t =
      deriv y t + ε * deriv f t :=
    (((hy.differentiable one_ne_zero t).hasDerivAt).add
      (((hf.differentiable one_ne_zero t).hasDerivAt).const_mul ε)).deriv
  have hiY := (hx.continuous.mul hy.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1
  have hiF := (hx.continuous.mul hf.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => (hx.differentiable one_ne_zero t).hasDerivAt)
    (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt)
    (hx.continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
    (hf.continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
  have hc : (∫ t in (0 : ℝ)..1, deriv x t * f t) =
      ∫ t in (0 : ℝ)..1, f t * deriv x t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hc, hxClosed, hfClosed, sub_self, zero_sub] at hb
  calc
    signedArea x (fun t => y t + ε * f t) =
        ∫ t in (0 : ℝ)..1, x t * deriv y t + ε * (x t * deriv f t) := by
      unfold signedArea
      apply intervalIntegral.integral_congr
      intro t _
      change x t * deriv (fun s => y s + ε * f s) t =
        x t * deriv y t + ε * (x t * deriv f t)
      rw [hd t]
      ring
    _ = signedArea x y + ε * ∫ t in (0 : ℝ)..1, x t * deriv f t := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul]
        rfl
      · exact hiY
      · exact hiF.const_mul ε
    _ = signedArea x y - ε * ∫ t in (0 : ℝ)..1, f t * deriv x t := by
      rw [hb]
      ring

/-- A horizontal shear changes signed area by the vertical line integral. -/
theorem horizontal_shear (x y f : ℝ → ℝ) (ε : ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hf : ContDiff ℝ 1 f) :
    signedArea (fun t => x t + ε * f t) y =
      signedArea x y + ε * ∫ t in (0 : ℝ)..1, f t * deriv y t := by
  have hiX := (hx.continuous.mul hy.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1
  have hiF := (hf.continuous.mul hy.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1
  calc
    signedArea (fun t => x t + ε * f t) y =
        ∫ t in (0 : ℝ)..1, x t * deriv y t + ε * (f t * deriv y t) := by
      unfold signedArea
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = signedArea x y + ε * ∫ t in (0 : ℝ)..1, f t * deriv y t := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul]
        rfl
      · exact hiX
      · exact hiF.const_mul ε


/-- A closed scalar path has zero integral against its own differential. -/
theorem closed_integral_self_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hclosed : f 0 = f 1) : (∫ t in (0 : ℝ)..1, f t * deriv f t) = 0 := by
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt)
    (fun t _ => (hf.differentiable one_ne_zero t).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
    (hf.continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
  have hc : (∫ t in (0 : ℝ)..1, deriv f t * f t) =
      ∫ t in (0 : ℝ)..1, f t * deriv f t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hc, hclosed, sub_self, zero_sub] at hb
  linarith

/-- Translating a closed curve in a fixed direction by a scalar path changes
its signed area by the corresponding normal line integral; the quadratic term vanishes. -/
theorem signedArea_perturb (x y f : ℝ → ℝ) (a b : ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y) (hf : ContDiff ℝ 1 f)
    (hxclosed : x 0 = x 1) (hfclosed : f 0 = f 1) :
    signedArea (fun t => x t + a * f t) (fun t => y t + b * f t) =
      signedArea x y + a * (∫ t in (0 : ℝ)..1, f t * deriv y t) -
        b * (∫ t in (0 : ℝ)..1, f t * deriv x t) := by
  have hfy : ContDiff ℝ 1 (fun t => y t + b * f t) := hy.add (contDiff_const.mul hf)
  rw [horizontal_shear x (fun t => y t + b * f t) f a hx hfy hf,
    vertical_shear x y f b hx hy hf hxclosed hfclosed]
  have hInt : (∫ t in (0 : ℝ)..1, f t * deriv (fun s => y s + b * f s) t) =
      ∫ t in (0 : ℝ)..1, f t * deriv y t := by
    have hd (t : ℝ) : deriv (fun s => y s + b * f s) t = deriv y t + b * deriv f t :=
      (((hy.differentiable one_ne_zero t).hasDerivAt).add
        (((hf.differentiable one_ne_zero t).hasDerivAt).const_mul b)).deriv
    calc
      _ = ∫ t in (0 : ℝ)..1, f t * deriv y t + b * (f t * deriv f t) := by
        apply intervalIntegral.integral_congr
        intro t _
        change f t * deriv (fun s => y s + b * f s) t = _
        rw [hd t]
        ring
      _ = (∫ t in (0 : ℝ)..1, f t * deriv y t) +
          b * ∫ t in (0 : ℝ)..1, f t * deriv f t := by
        rw [intervalIntegral.integral_add]
        · rw [intervalIntegral.integral_const_mul]
        · exact (hf.continuous.mul hy.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1
        · exact ((hf.continuous.mul hf.continuous_deriv_one).intervalIntegrable (μ := volume) 0 1).const_mul b
      _ = _ := by rw [closed_integral_self_deriv f hf hfclosed, mul_zero, add_zero]
  rw [hInt]
  ring

open ContinuousLinearMap

/-- The vertical shear has Jacobian determinant `1 + ε ∂y P`. -/
theorem vertical_shear_det (L : (ℝ × ℝ) →L[ℝ] ℝ) (ε : ℝ) :
    ((fst ℝ ℝ ℝ).prod ((snd ℝ ℝ ℝ) + ε • L)).toLinearMap.det =
      1 + ε * L (0, 1) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]

/-- Derivative of the vertical shear, assuming differentiability only at the point. -/
theorem vertical_shear_hasFDerivAt (P : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (ε : ℝ)
    (hP : DifferentiableAt ℝ P z) :
    HasFDerivAt (fun w : ℝ × ℝ => (w.1, w.2 + ε * P w))
      ((fst ℝ ℝ ℝ).prod ((snd ℝ ℝ ℝ) + ε • fderiv ℝ P z)) z := by
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
      ((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).add (hP.hasFDerivAt.const_smul ε))

/-- The horizontal shear has Jacobian determinant `1 + ε ∂x Q`. -/
theorem horizontal_shear_det (L : (ℝ × ℝ) →L[ℝ] ℝ) (ε : ℝ) :
    (((fst ℝ ℝ ℝ) + ε • L).prod (snd ℝ ℝ ℝ)).toLinearMap.det =
      1 + ε * L (1, 0) := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]

/-- Derivative of the horizontal shear, assuming differentiability only at the point. -/
theorem horizontal_shear_hasFDerivAt (Q : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (ε : ℝ)
    (hQ : DifferentiableAt ℝ Q z) :
    HasFDerivAt (fun w : ℝ × ℝ => (w.1 + ε * Q w, w.2))
      (((fst ℝ ℝ ℝ) + ε • fderiv ℝ Q z).prod (snd ℝ ℝ ℝ)) z := by
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).add
      (hQ.hasFDerivAt.const_smul ε)).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := z))

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.curve_mapsTo_neighborhood
#check_upstream ClassicalTheorems.Progress.Green.line_integrable
#check_upstream ClassicalTheorems.Progress.Green.curl_integrable
#check_upstream ClassicalTheorems.Progress.Green.one_form_coordinates
#check_upstream ClassicalTheorems.Progress.Green.exact_closed_curve

#check_upstream ClassicalTheorems.Progress.Green.rectangle

#check_upstream ClassicalTheorems.Progress.Green.vertical_shear
#check_upstream ClassicalTheorems.Progress.Green.horizontal_shear

#check_upstream ClassicalTheorems.Progress.Green.vertical_shear_det
#check_upstream ClassicalTheorems.Progress.Green.vertical_shear_hasFDerivAt
#check_upstream ClassicalTheorems.Progress.Green.horizontal_shear_det
#check_upstream ClassicalTheorems.Progress.Green.horizontal_shear_hasFDerivAt

#check_upstream ClassicalTheorems.Progress.Green.closed_integral_self_deriv
#check_upstream ClassicalTheorems.Progress.Green.signedArea_perturb

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenOrientation
import ClassicalTheorems.Progress.GreenGeometry
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Verified results for the area step of Green’s theorem. The full arbitrary-field identity
is proved in `ClassicalTheorems.Progress.GreenFull`. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Green

/-- Green's area case under the domain, curve and winding hypotheses of Green’s theorem. -/
theorem complex_signedArea_eq_domain_area (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) = (volume D).toReal := by
  let e := Complex.orthonormalBasisOneI.repr
  let δ : ℝ → Point := e ∘ γ
  let E : Set Point := e '' D
  let Γ : Set Point := δ '' Icc 0 1
  have hd : ContDiff ℝ 1 δ := e.toContinuousLinearMap.contDiff.comp hCurve
  have hclosed : δ 0 = δ 1 := congrArg e hClosed
  have hinj : InjOn δ (Ico 0 1) := e.injective.comp_injOn hSimple
  have hJordan : IsJordanCurve Γ :=
    isJordanCurve_of_simple_closed δ hd.continuous.continuousOn hclosed hinj
  have hfront : frontier E = Γ := by
    calc
      frontier E = e '' frontier D := (e.toHomeomorph.image_frontier D).symm
      _ = Γ := by rw [hBoundary, image_image]; rfl
  have hEopen : IsOpen E := e.toHomeomorph.isOpenMap D hDomain
  have hEconn : IsConnected E := hConnected.image e e.continuous.continuousOn
  have hEbdd : Bornology.IsBounded E := e.lipschitz.isBounded_image hBounded
  have hE : E = jordanInterior Γ := by
    have hJ : IsJordanCurve (frontier E) := hfront.symm ▸ hJordan
    simpa only [hfront] using domain_eq_jordanInterior E hEopen hEconn hEbdd hJ
  have horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => δ t) := by
    refine ⟨by norm_num, hJordan, hd.continuous.comp continuous_subtype_val,
      range_domRestrict δ (Icc 0 1), hclosed, ?_, ?_⟩
    · intro s hs t ht heq
      apply Subtype.ext
      exact hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq
    · intro p hp
      have hpE : p ∈ E := hE.symm ▸ hp
      obtain ⟨z, hz, rfl⟩ := hpE
      have hzcurve : z ∉ γ '' Icc 0 1 := by
        rw [← hBoundary]
        exact fun hzf => (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hDomain)) hzf hz
      have hw := complex_curveWinding_integral γ hCurve hClosed hSimple z hzcurve
      rw [hPositive z hz] at hw
      have hpi : 2 * Real.pi ≠ 0 := by positivity
      apply mul_left_cancel₀ hpi
      simpa only [δ, e, Function.comp_apply, Bool.true_eq_false, ↓reduceIte, mul_one] using hw
  have hArea := c1_signedArea_eq_jordanInterior_area δ hd Γ horiented
  have hMeasure : volume E = volume D := by
    have hm := e.symm.measurePreserving.measure_preimage hDomain.measurableSet.nullMeasurableSet
    have heq : e.symm ⁻¹' D = E := by
      ext p
      constructor
      · intro hp
        exact ⟨e.symm p, hp, e.apply_symm_apply p⟩
      · rintro ⟨z, hz, rfl⟩
        simpa using hz
    rwa [heq] at hm
  calc
    (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
        signedArea (fun t => δ t 0) (fun t => δ t 1) := by
      unfold signedArea
      apply intervalIntegral.integral_congr
      intro t _
      have hdim : deriv (fun s => δ s 1) t = (deriv γ t).im := by
        simpa [δ, e] using deriv_im γ hCurve t
      change (γ t).re * (deriv γ t).im = δ t 0 * deriv (fun s => δ s 1) t
      rw [hdim]
      simp [δ, e]
    _ = ClassicalResults.area (jordanInterior Γ) := hArea
    _ = (volume D).toReal := by rw [← hE, ClassicalResults.area, hMeasure]

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.complex_signedArea_eq_domain_area

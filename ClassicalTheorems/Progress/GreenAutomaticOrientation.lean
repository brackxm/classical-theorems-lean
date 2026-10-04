/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.Orientation
import ClassicalTheorems.Progress.GreenFull
import ClassicalTheorems.Progress.SchoenfliesWinding

/-! Green's theorem with orientation constructed from a simple closed boundary.
The sign is uniform throughout the domain and applies to every coefficient pair. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Green

/-- A C¹ Jordan boundary has a uniform winding sign on its bounded connected domain. -/
theorem complex_domain_winding_sign (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1)) :
    ∃ orientation : Bool, ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) =
        if orientation then 2 * Real.pi else -(2 * Real.pi) := by
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
  have hE : E = jordanInterior Γ := by
    have hJ : IsJordanCurve (frontier E) := hfront.symm ▸ hJordan
    simpa only [hfront] using domain_eq_jordanInterior E
      (e.toHomeomorph.isOpenMap D hDomain)
      (hConnected.image e e.continuous.continuousOn)
      (e.lipschitz.isBounded_image hBounded) hJ
  have hi : InjOn (fun t : Icc (0 : ℝ) 1 => δ t) {t | (t : ℝ) < 1} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨orientation, ho⟩ := Isoperimetric.simple_jordan_is_oriented
    (by norm_num : (0 : ℝ) < 1) (fun t : Icc (0 : ℝ) 1 => δ t) Γ hJordan
    (hd.continuous.comp continuous_subtype_val) (range_domRestrict δ _) hclosed hi
  refine ⟨orientation, fun z hz => ?_⟩
  have hzcurve : z ∉ γ '' Icc 0 1 := by
    rw [← hBoundary]
    exact fun hzf => (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hDomain)) hzf hz
  have hzE : e z ∈ E := ⟨z, hz, rfl⟩
  have hw := ho.2.2.2.2.2.2 (e z) (hE ▸ hzE)
  have hint := complex_curveWinding_integral γ hCurve hClosed hSimple z hzcurve
  change 2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
    (fun t : Icc (0 : ℝ) 1 => δ t) (e z) = _ at hint
  rw [hw] at hint
  cases orientation <;> simpa using hint.symm

/-- Reversing a C¹ curve negates its derivative at the reversed parameter. -/
theorem deriv_reverse_complex (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (t : ℝ) :
    deriv (fun s => γ (1 - s)) t = -deriv γ (1 - t) := by
  have hr : HasDerivAt (fun s : ℝ => 1 - s) (-1 : ℝ) t := by
    simpa only [id_eq] using (hasDerivAt_id t).const_sub 1
  have h := ((hγ.differentiable one_ne_zero (1 - t)).hasDerivAt).scomp t hr
  simpa only [Function.comp_def, neg_one_smul] using h.deriv

/-- Parameter reversal negates the entire winding integral. -/
theorem complex_winding_integral_reverse (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (z : ℂ) :
    (∫ t in (0 : ℝ)..1, (deriv (fun s => γ (1 - s)) t / (γ (1 - t) - z)).im) =
      -(∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) := by
  simp_rw [deriv_reverse_complex γ hγ, neg_div, Complex.neg_im]
  rw [intervalIntegral.integral_neg]
  congr 1
  simpa using intervalIntegral.integral_comp_sub_left
    (fun t => (deriv γ t / (γ t - z)).im) (a := (0 : ℝ)) (b := 1) 1

/-- Parameter reversal negates a coefficient-weighted boundary integral. -/
theorem complex_line_integral_reverse (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (P Q : ℂ → ℝ) :
    (∫ t in (0 : ℝ)..1,
      P (γ (1 - t)) * (deriv (fun s => γ (1 - s)) t).re +
      Q (γ (1 - t)) * (deriv (fun s => γ (1 - s)) t).im) =
      -(∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  simp_rw [deriv_reverse_complex γ hγ, Complex.neg_re, Complex.neg_im,
    mul_neg, ← neg_add]
  rw [intervalIntegral.integral_neg]
  congr 1
  simpa using intervalIntegral.integral_comp_sub_left
    (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im)
    (a := (0 : ℝ)) (b := 1) 1

/-- The reversed boundary has exactly the same image and remains simple before its endpoint. -/
theorem complex_reverse_boundary (γ : ℝ → ℂ)
    (hClosed : γ 0 = γ 1) (hSimple : InjOn γ (Ico 0 1)) :
    (fun t => γ (1 - t)) '' Icc (0 : ℝ) 1 = γ '' Icc 0 1 ∧
      InjOn (fun t => γ (1 - t)) (Ico (0 : ℝ) 1) := by
  constructor
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      exact congrArg γ (by ring)
  · let e := Complex.orthonormalBasisOneI.repr
    let x : Icc (0 : ℝ) 1 → Point := fun t => e (γ t)
    have hc : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩ := congrArg e hClosed
    have hi : InjOn x {t | (t : ℝ) < 1} := by
      intro s hs t ht he
      exact Subtype.ext (hSimple ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ (e.injective he))
    have hir := Isoperimetric.jordan_injOn_right_halfopen x hc hi
    intro s hs t ht he
    have h := hir (x₁ := ⟨1 - s, by constructor <;> linarith [hs.1, hs.2]⟩)
      (x₂ := ⟨1 - t, by constructor <;> linarith [ht.1, ht.2]⟩)
      (by change 0 < 1 - s; linarith [hs.2])
      (by change 0 < 1 - t; linarith [ht.2]) (congrArg e he)
    have h' := congrArg Subtype.val h
    dsimp at h'
    linarith

/-- Green's theorem in either direction, with the sign constructed once from the boundary.
The same sign works for every C¹ coefficient pair, including at stationary curve points. -/
theorem greens_theorem_either_orientation (D U : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1)) :
    ∃ orientation : Bool,
      (∀ z ∈ D, (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) =
        if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
          (if orientation then 1 else -1) *
            ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw⟩ := complex_domain_winding_sign D γ
    hDomain hBounded hConnected hBoundary hCurve hClosed hSimple
  refine ⟨orientation, hw, fun P Q hP hQ => ?_⟩
  cases orientation with
  | true =>
      simpa using greens_theorem_without_regularity D U γ P Q hDomain hBounded hConnected
        hBoundary hOpen hNeighborhood hCurve hClosed hSimple hw hP hQ
  | false =>
      let δ : ℝ → ℂ := fun t => γ (1 - t)
      have hδ : ContDiff ℝ 1 δ := hCurve.comp (contDiff_const.sub contDiff_id)
      have hcδ : δ 0 = δ 1 := by simpa [δ] using hClosed.symm
      obtain ⟨hrδ, hiδ⟩ := complex_reverse_boundary γ hClosed hSimple
      have hbδ : frontier D = δ '' Icc 0 1 := hBoundary.trans hrδ.symm
      have hwδ (z : ℂ) (hz : z ∈ D) :
          (∫ t in (0 : ℝ)..1, (deriv δ t / (δ t - z)).im) = 2 * Real.pi := by
        rw [complex_winding_integral_reverse γ hCurve z, hw z hz]
        simp
      have h := greens_theorem_without_regularity D U δ P Q hDomain hBounded hConnected
        hbδ hOpen hNeighborhood hδ hcδ hiδ hwδ hP hQ
      rw [complex_line_integral_reverse γ hCurve P Q] at h
      simp only [Bool.false_eq_true, ite_false, neg_one_mul]
      linarith

/-- One positive winding check fixes the sign throughout the domain and for every field. -/
theorem greens_theorem_of_positive_winding_at (D U : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1)) (z : ℂ) (hz : z ∈ D)
    (hPositive : (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_either_orientation D U γ
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- The magnitude of Green's identity is independent of traversal direction. -/
theorem greens_theorem_abs (D U : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_either_orientation D U γ
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.complex_domain_winding_sign
#check_upstream ClassicalTheorems.Progress.Green.deriv_reverse_complex
#check_upstream ClassicalTheorems.Progress.Green.complex_winding_integral_reverse
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_reverse
#check_upstream ClassicalTheorems.Progress.Green.complex_reverse_boundary
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_either_orientation

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_of_positive_winding_at
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_abs

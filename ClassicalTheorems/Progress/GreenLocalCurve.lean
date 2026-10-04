/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenInterval

/-! Green's theorem for curves that are C¹ only on a neighborhood of the
parameter interval. A smooth cutoff preserves boundary values and derivatives. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Green

/-- Local C¹ regularity near a compact interval gives a global C¹ curve with the
same values and actual derivatives on the interval, including its endpoints. -/
theorem exists_c1_curve_extension (γ : ℝ → ℂ) {a b : ℝ} (V : Set ℝ)
    (hV : IsOpen V) (hInterval : Icc a b ⊆ V) (hγ : ContDiffOn ℝ 1 γ V) :
    ∃ δ : ℝ → ℂ, ContDiff ℝ 1 δ ∧ EqOn δ γ (Icc a b) ∧
      EqOn (deriv δ) (deriv γ) (Icc a b) := by
  obtain ⟨δ, W, hδ, _, hW, hIW, he⟩ :=
    exists_compactSupport_extension_vector (Icc a b) V isCompact_Icc hV hInterval γ hγ
  refine ⟨δ, hδ, he.mono hIW, ?_⟩
  intro t ht
  apply Filter.EventuallyEq.deriv_eq
  exact Filter.mem_of_superset (hW.mem_nhds (hIW ht)) (fun s hs => he hs)

/-- Curves agreeing in value and derivative on the integration interval have
identical coefficient-weighted line integrals. -/
theorem complex_line_integral_eq_of_eqOn (γ δ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (he : EqOn δ γ (Icc a b)) (hd : EqOn (deriv δ) (deriv γ) (Icc a b))
    (P Q : ℂ → ℝ) :
    (∫ t in a..b, P (δ t) * (deriv δ t).re + Q (δ t) * (deriv δ t).im) =
      ∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  dsimp only
  rw [he ht, hd ht]

/-- The same local agreement preserves the complex winding integral. -/
theorem complex_winding_integral_eq_of_eqOn (γ δ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (he : EqOn δ γ (Icc a b)) (hd : EqOn (deriv δ) (deriv γ) (Icc a b)) (z : ℂ) :
    (∫ t in a..b, (deriv δ t / (δ t - z)).im) =
      ∫ t in a..b, (deriv γ t / (γ t - z)).im := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  dsimp only
  rw [he ht, hd ht]

/-- Signed Green with C¹ regularity required only on an open neighborhood of
[a,b]. The boundary constructs one orientation for every coefficient pair. -/
theorem greens_theorem_local_curve (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b) (V : Set ℝ) (hV : IsOpen V) (hInterval : Icc a b ⊆ V)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b)) :
    ∃ orientation : Bool,
      (∀ z ∈ D, (∫ t in a..b, (deriv γ t / (γ t - z)).im) =
        if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        (∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
          (if orientation then 1 else -1) *
            ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨δ, hδ, he, hd⟩ := exists_c1_curve_extension γ V hV hInterval hCurve
  have hb : frontier D = δ '' Icc a b := hBoundary.trans he.image_eq.symm
  have hc : δ a = δ b := by
    rw [he ⟨le_rfl, hab.le⟩, he ⟨hab.le, le_rfl⟩, hClosed]
  have hi : InjOn δ (Ico a b) := (he.mono Ico_subset_Icc_self).injOn_iff.mpr hSimple
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_interval D U δ hab
    hDomain hBounded hConnected hb hOpen hNeighborhood hδ hc hi
  refine ⟨orientation, fun z hz => ?_, fun P Q hP hQ => ?_⟩
  · rw [← complex_winding_integral_eq_of_eqOn γ δ hab.le he hd z]
    exact hw z hz
  · rw [← complex_line_integral_eq_of_eqOn γ δ hab.le he hd P Q]
    exact hg P Q hP hQ

/-- One positive winding check fixes the sign for a locally C¹ boundary curve. -/
theorem greens_theorem_local_curve_of_positive_winding_at (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b) (V : Set ℝ) (hV : IsOpen V) (hInterval : Icc a b ⊆ V)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b)) (z : ℂ) (hz : z ∈ D)
    (hPositive : (∫ t in a..b, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_local_curve D U γ hab V hV hInterval
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Orientation-independent Green for a boundary curve C¹ only near [a,b]. -/
theorem greens_theorem_local_curve_abs (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b) (V : Set ℝ) (hV : IsOpen V) (hInterval : Icc a b ⊆ V)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b))
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_local_curve D U γ hab V hV hInterval
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.exists_c1_curve_extension
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_eq_of_eqOn
#check_upstream ClassicalTheorems.Progress.Green.complex_winding_integral_eq_of_eqOn
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_local_curve
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_local_curve_of_positive_winding_at
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_local_curve_abs

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenAutomaticOrientation

/-! Green's theorem on any nondegenerate compact parameter interval.
Affine normalization preserves boundary geometry, winding and line integrals. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Green

/-- Change of variables for affine normalization, with its derivative included. -/
theorem integral_affine_unit (f : ℝ → ℝ) (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, (b - a) * f (a + (b - a) * t)) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_add_mul f
    (a := (0 : ℝ)) (b := 1) (b - a) a
  rw [show a + (b - a) * 0 = a by ring,
    show a + (b - a) * 1 = b by ring] at h
  exact h

/-- The derivative of an affinely normalized C¹ complex curve. -/
theorem deriv_affine_complex (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (a b t : ℝ) :
    deriv (fun s => γ (a + (b - a) * s)) t =
      (b - a) • deriv γ (a + (b - a) * t) := by
  have hu : HasDerivAt (fun s : ℝ => a + (b - a) * s) (b - a) t := by
    simpa using ((hasDerivAt_id t).const_mul (b - a)).const_add a
  have h := ((hγ.differentiable one_ne_zero (a + (b - a) * t)).hasDerivAt).scomp t hu
  simpa only [Function.comp_def] using h.deriv

/-- Affine normalization preserves every coefficient-weighted boundary integral. -/
theorem complex_line_integral_affine (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (P Q : ℂ → ℝ) (a b : ℝ) :
    (∫ t in (0 : ℝ)..1,
      P (γ (a + (b - a) * t)) * (deriv (fun s => γ (a + (b - a) * s)) t).re +
      Q (γ (a + (b - a) * t)) * (deriv (fun s => γ (a + (b - a) * s)) t).im) =
      ∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  rw [← integral_affine_unit
    (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) a b]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [deriv_affine_complex γ hγ a b t]
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- Affine normalization preserves the complex winding integral. -/
theorem complex_winding_integral_affine (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (z : ℂ) (a b : ℝ) :
    (∫ t in (0 : ℝ)..1,
      (deriv (fun s => γ (a + (b - a) * s)) t / (γ (a + (b - a) * t) - z)).im) =
      ∫ t in a..b, (deriv γ t / (γ t - z)).im := by
  rw [← integral_affine_unit (fun t => (deriv γ t / (γ t - z)).im) a b]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [deriv_affine_complex γ hγ a b t, smul_div_assoc, Complex.smul_im, smul_eq_mul]

/-- An increasing affine clock covers the compact interval exactly. -/
theorem affine_unit_image {a b : ℝ} (hab : a < b) :
    (fun t : ℝ => a + (b - a) * t) '' Icc (0 : ℝ) 1 = Icc a b := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor <;> nlinarith [hs.1, hs.2]
  · intro ht
    refine ⟨(t - a) / (b - a), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
    · field_simp [sub_ne_zero.mpr hab.ne']
      ring

/-- Increasing affine normalization preserves simplicity before the terminal endpoint. -/
theorem complex_simple_affine (γ : ℝ → ℂ) {a b : ℝ} (hab : a < b)
    (hi : InjOn γ (Ico a b)) :
    InjOn (fun t => γ (a + (b - a) * t)) (Ico (0 : ℝ) 1) := by
  intro s hs t ht he
  have h := hi (x₁ := a + (b - a) * s) (x₂ := a + (b - a) * t)
    (by constructor <;> nlinarith [hs.1, hs.2])
    (by constructor <;> nlinarith [ht.1, ht.2]) he
  nlinarith

/-- Signed Green on any compact interval, with one automatically constructed sign
for every C¹ coefficient pair and no nonzero-speed hypothesis. -/
theorem greens_theorem_interval (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b)) :
    ∃ orientation : Bool,
      (∀ z ∈ D, (∫ t in a..b, (deriv γ t / (γ t - z)).im) =
        if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        (∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
          (if orientation then 1 else -1) *
            ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  let δ : ℝ → ℂ := fun t => γ (a + (b - a) * t)
  have hδ : ContDiff ℝ 1 δ := hCurve.comp (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hcδ : δ 0 = δ 1 := by simpa [δ] using hClosed
  have hbδ : frontier D = δ '' Icc (0 : ℝ) 1 := by
    change frontier D = (γ ∘ (fun t => a + (b - a) * t)) '' Icc (0 : ℝ) 1
    calc
      frontier D = γ '' Icc a b := hBoundary
      _ = γ '' ((fun t : ℝ => a + (b - a) * t) '' Icc (0 : ℝ) 1) := by
        rw [affine_unit_image hab]
      _ = _ := image_image γ _ _
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_either_orientation D U δ
    hDomain hBounded hConnected hbδ hOpen hNeighborhood hδ hcδ
    (complex_simple_affine γ hab hSimple)
  refine ⟨orientation, fun z hz => ?_, fun P Q hP hQ => ?_⟩
  · rw [← complex_winding_integral_affine γ hCurve z a b]
    exact hw z hz
  · rw [← complex_line_integral_affine γ hCurve P Q a b]
    exact hg P Q hP hQ

/-- A single positive winding check gives the usual Green formula on any compact interval. -/
theorem greens_theorem_interval_of_positive_winding_at (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b)) (z : ℂ) (hz : z ∈ D)
    (hPositive : (∫ t in a..b, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_interval D U γ hab
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Green's magnitude identity on any compact interval, independent of orientation. -/
theorem greens_theorem_interval_abs (D U : Set ℂ) (γ : ℝ → ℂ)
    {a b : ℝ} (hab : a < b)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc a b)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ a = γ b)
    (hSimple : InjOn γ (Ico a b))
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_interval D U γ hab
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.integral_affine_unit
#check_upstream ClassicalTheorems.Progress.Green.deriv_affine_complex
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_affine
#check_upstream ClassicalTheorems.Progress.Green.complex_winding_integral_affine
#check_upstream ClassicalTheorems.Progress.Green.affine_unit_image
#check_upstream ClassicalTheorems.Progress.Green.complex_simple_affine
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_interval
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_interval_of_positive_winding_at
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_interval_abs

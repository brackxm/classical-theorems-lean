/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenLocalCurve
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Nonlinear change of clock for Green's theorem. The clock need not be
injective or monotone: pauses and retraced portions cancel in the line integral. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Green

/-- Substitution for a clock C¹ only near its integration interval. No
monotonicity or nonzero-derivative assumption is needed. -/
theorem integral_local_clock (φ f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (W : Set ℝ) (hW : IsOpen W) (hInterval : Icc a b ⊆ W)
    (hφ : ContDiffOn ℝ 1 φ W) (hf : ContinuousOn f (φ '' Icc a b)) :
    (∫ t in a..b, deriv φ t * f (φ t)) = ∫ s in φ a..φ b, f s := by
  simpa only [uIcc_of_le hab, smul_eq_mul, Function.comp_def] using
    intervalIntegral.integral_deriv_smul_comp'
      (f := φ) (f' := deriv φ) (g := f)
      (a := a) (b := b)
      (fun t ht => ((hφ.contDiffAt (hW.mem_nhds
        (hInterval (by simpa only [uIcc_of_le hab] using ht)))).differentiableAt
          one_ne_zero).hasDerivAt)
      (by simpa only [uIcc_of_le hab] using
        (hφ.continuousOn_deriv_of_isOpen hW le_rfl).mono hInterval)
      (by simpa only [uIcc_of_le hab] using hf)

/-- The local chain rule for a complex curve and a real clock. -/
theorem deriv_comp_complex_local (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    (V W : Set ℝ) (hV : IsOpen V) (hW : IsOpen W)
    (hγ : ContDiffOn ℝ 1 γ V) (hφ : ContDiffOn ℝ 1 φ W)
    {t : ℝ} (ht : t ∈ W) (hφt : φ t ∈ V) :
    deriv (γ ∘ φ) t = deriv φ t • deriv γ (φ t) := by
  exact deriv.scomp t
    ((hγ.contDiffAt (hV.mem_nhds hφt)).differentiableAt one_ne_zero)
    ((hφ.contDiffAt (hW.mem_nhds ht)).differentiableAt one_ne_zero)

/-- Nonlinear substitution preserves the line integral, even when the clock
pauses or retraces. Both maps need be C¹ only near the visited parameters. -/
theorem complex_line_integral_reparam (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (V W : Set ℝ) (U : Set ℂ)
    (hV : IsOpen V) (hW : IsOpen W)
    (hγ : ContDiffOn ℝ 1 γ V) (hφ : ContDiffOn ℝ 1 φ W)
    (hInterval : Icc a b ⊆ W) (hImage : φ '' Icc a b ⊆ V)
    (hFieldImage : MapsTo γ (φ '' Icc a b) U)
    (P Q : ℂ → ℝ) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) :
    (∫ t in a..b, P ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).re +
      Q ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).im) =
      ∫ s in φ a..φ b, P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  let f : ℝ → ℝ := fun s => P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im
  have hc := hγ.continuousOn.mono hImage
  have hd := (hγ.continuousOn_deriv_of_isOpen hV le_rfl).mono hImage
  have hf : ContinuousOn f (φ '' Icc a b) :=
    ((hP.comp hc hFieldImage).mul (Complex.continuous_re.comp_continuousOn hd)).add
      ((hQ.comp hc hFieldImage).mul (Complex.continuous_im.comp_continuousOn hd))
  calc
    _ = ∫ t in a..b, deriv φ t * f (φ t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [deriv_comp_complex_local γ φ V W hV hW hγ hφ
        (hInterval ht) (hImage ⟨t, ht, rfl⟩)]
      simp only [Function.comp_def, Complex.smul_re, Complex.smul_im, smul_eq_mul, f]
      ring
    _ = _ := integral_local_clock φ f hab W hW hInterval hφ hf

/-- Nonlinear substitution preserves winding integrals at points avoided by
the curve; the clock may have zero or negative derivative. -/
theorem complex_winding_integral_reparam (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    {a b : ℝ} (hab : a ≤ b) (V W : Set ℝ) (hV : IsOpen V) (hW : IsOpen W)
    (hγ : ContDiffOn ℝ 1 γ V) (hφ : ContDiffOn ℝ 1 φ W)
    (hInterval : Icc a b ⊆ W) (hImage : φ '' Icc a b ⊆ V)
    (z : ℂ) (hAvoid : ∀ s ∈ φ '' Icc a b, γ s - z ≠ 0) :
    (∫ t in a..b, (deriv (γ ∘ φ) t / ((γ ∘ φ) t - z)).im) =
      ∫ s in φ a..φ b, (deriv γ s / (γ s - z)).im := by
  let f : ℝ → ℝ := fun s => (deriv γ s / (γ s - z)).im
  have hc := hγ.continuousOn.mono hImage
  have hd := (hγ.continuousOn_deriv_of_isOpen hV le_rfl).mono hImage
  have hf : ContinuousOn f (φ '' Icc a b) :=
    Complex.continuous_im.comp_continuousOn (hd.div (hc.sub continuousOn_const) hAvoid)
  calc
    _ = ∫ t in a..b, deriv φ t * f (φ t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [deriv_comp_complex_local γ φ V W hV hW hγ hφ
        (hInterval ht) (hImage ⟨t, ht, rfl⟩)]
      simp only [Function.comp_def, smul_div_assoc, Complex.smul_im, smul_eq_mul, f]
    _ = _ := integral_local_clock φ f hab W hW hInterval hφ hf

/-- Green after any locally C¹ clock covering the original parameter endpoints
and staying in the original interval. Injectivity and monotonicity of the clock
are unnecessary: signed contributions of retraced portions cancel. -/
theorem greens_theorem_reparametrized (D U : Set ℂ) (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (V W : Set ℝ) (hV : IsOpen V) (hW : IsOpen W)
    (hCurveInterval : Icc c d ⊆ V) (hClockInterval : Icc a b ⊆ W)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClock : ContDiffOn ℝ 1 φ W)
    (hClockImage : MapsTo φ (Icc a b) (Icc c d)) (hStart : φ a = c) (hFinish : φ b = d)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc c d)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hClosed : γ c = γ d) (hSimple : InjOn γ (Ico c d)) :
    ∃ orientation : Bool,
      (∀ z ∈ D, (∫ t in a..b, (deriv (γ ∘ φ) t / ((γ ∘ φ) t - z)).im) =
        if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        (∫ t in a..b, P ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).re +
          Q ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).im) =
          (if orientation then 1 else -1) *
            ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  have hImage : φ '' Icc a b ⊆ Icc c d := by
    rintro _ ⟨t, ht, rfl⟩
    exact hClockImage ht
  have hFieldImage : MapsTo γ (φ '' Icc a b) U := by
    intro s hs
    apply hNeighborhood
    apply frontier_subset_closure
    rw [hBoundary]
    exact ⟨s, hImage hs, rfl⟩
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_local_curve D U γ hcd V hV hCurveInterval
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hCurve hClosed hSimple
  refine ⟨orientation, fun z hz => ?_, fun P Q hP hQ => ?_⟩
  · have hAvoid : ∀ s ∈ φ '' Icc a b, γ s - z ≠ 0 := by
      intro s hs he
      have hzBoundary : z ∈ frontier D := by
        rw [hBoundary]
        exact ⟨s, hImage hs, sub_eq_zero.mp he⟩
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hDomain) hzBoundary hz
    rw [complex_winding_integral_reparam γ φ hab.le V W hV hW hCurve hClock
      hClockInterval (hImage.trans hCurveInterval) z hAvoid, hStart, hFinish]
    exact hw z hz
  · rw [complex_line_integral_reparam γ φ hab.le V W U hV hW hCurve hClock
      hClockInterval (hImage.trans hCurveInterval) hFieldImage P Q
      hP.continuousOn hQ.continuousOn, hStart, hFinish]
    exact hg P Q hP hQ

/-- One positive winding check gives the usual Green formula after a nonlinear
clock, including clocks that pause or retrace. -/
theorem greens_theorem_reparametrized_of_positive_winding_at (D U : Set ℂ) (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (V W : Set ℝ) (hV : IsOpen V) (hW : IsOpen W)
    (hCurveInterval : Icc c d ⊆ V) (hClockInterval : Icc a b ⊆ W)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClock : ContDiffOn ℝ 1 φ W)
    (hClockImage : MapsTo φ (Icc a b) (Icc c d)) (hStart : φ a = c) (hFinish : φ b = d)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc c d)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hClosed : γ c = γ d) (hSimple : InjOn γ (Ico c d)) (z : ℂ) (hz : z ∈ D)
    (hPositive : (∫ t in a..b, (deriv (γ ∘ φ) t / ((γ ∘ φ) t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in a..b, P ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).re +
      Q ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_reparametrized D U γ φ hab hcd V W hV hW
    hCurveInterval hClockInterval hCurve hClock hClockImage hStart hFinish
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hClosed hSimple
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Green's magnitude identity after a nonlinear clock, without an orientation input. -/
theorem greens_theorem_reparametrized_abs (D U : Set ℂ) (γ : ℝ → ℂ) (φ : ℝ → ℝ)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (V W : Set ℝ) (hV : IsOpen V) (hW : IsOpen W)
    (hCurveInterval : Icc c d ⊆ V) (hClockInterval : Icc a b ⊆ W)
    (hCurve : ContDiffOn ℝ 1 γ V) (hClock : ContDiffOn ℝ 1 φ W)
    (hClockImage : MapsTo φ (Icc a b) (Icc c d)) (hStart : φ a = c) (hFinish : φ b = d)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc c d)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hClosed : γ c = γ d) (hSimple : InjOn γ (Ico c d))
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∫ t in a..b, P ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).re +
      Q ((γ ∘ φ) t) * (deriv (γ ∘ φ) t).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_reparametrized D U γ φ hab hcd V W hV hW
    hCurveInterval hClockInterval hCurve hClock hClockImage hStart hFinish
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood hClosed hSimple
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

/-- A polynomial clock from 0 to 1 with zero speed at both endpoints. -/
def endpointPauseClock (t : ℝ) : ℝ := 3 * t ^ 2 - 2 * t ^ 3

@[simp] theorem endpointPauseClock_zero : endpointPauseClock 0 = 0 := by
  norm_num [endpointPauseClock]

@[simp] theorem endpointPauseClock_one : endpointPauseClock 1 = 1 := by
  norm_num [endpointPauseClock]

/-- The endpoint-pause clock is globally C¹. -/
theorem endpointPauseClock_contDiff : ContDiff ℝ 1 endpointPauseClock := by
  unfold endpointPauseClock
  fun_prop

/-- Its derivative is 6t(1−t), so the clock stops at both endpoints. -/
theorem endpointPauseClock_hasDerivAt (t : ℝ) :
    HasDerivAt endpointPauseClock (6 * t * (1 - t)) t := by
  have h := (((hasDerivAt_id t).pow 2).const_mul 3).sub
    (((hasDerivAt_id t).pow 3).const_mul 2)
  convert h using 1
  · rfl
  · norm_num
    ring

/-- The endpoint-pause clock stays in the unit interval. -/
theorem endpointPauseClock_mapsTo : MapsTo endpointPauseClock (Icc 0 1) (Icc 0 1) := by
  intro t ht
  dsimp only [mem_Icc, endpointPauseClock]
  constructor
  · have h := mul_nonneg (sq_nonneg t) (show 0 ≤ 3 - 2 * t by linarith [ht.2])
    nlinarith
  · have h := mul_nonneg (sq_nonneg (1 - t)) (show 0 ≤ 1 + 2 * t by linarith [ht.1])
    nlinarith

/-- Endpoint stops do not spoil injectivity: the polynomial clock is strictly
increasing on the whole closed unit interval. -/
theorem endpointPauseClock_strictMonoOn : StrictMonoOn endpointPauseClock (Icc 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) endpointPauseClock_contDiff.continuous.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  rw [(endpointPauseClock_hasDerivAt t).deriv]
  exact mul_pos (mul_pos (by norm_num) ht.1) (sub_pos.mpr ht.2)

/-- The polynomial clock covers the unit interval exactly. -/
theorem endpointPauseClock_image : endpointPauseClock '' Icc 0 1 = Icc 0 1 := by
  simpa only [endpointPauseClock_zero, endpointPauseClock_one] using
    endpointPauseClock_contDiff.continuous.continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) endpointPauseClock_strictMonoOn.monotoneOn

/-- Slowing any C¹ curve with this clock makes its endpoint derivatives zero. -/
theorem deriv_endpointPauseClock_comp (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) :
    deriv (γ ∘ endpointPauseClock) 0 = 0 ∧ deriv (γ ∘ endpointPauseClock) 1 = 0 := by
  have hd (t : ℝ) := deriv.scomp t
    (hγ.differentiable one_ne_zero (endpointPauseClock t))
    (endpointPauseClock_contDiff.differentiable one_ne_zero t)
  constructor
  · rw [hd, (endpointPauseClock_hasDerivAt 0).deriv]
    simp
  · rw [hd, (endpointPauseClock_hasDerivAt 1).deriv]
    simp

/-- The concrete endpoint-pause clock leaves every continuous-coefficient line
integral unchanged while giving the composed curve zero speed at its endpoints. -/
theorem complex_line_integral_endpointPauseClock (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (P Q : ℂ → ℝ) (hP : ContinuousOn P (γ '' Icc 0 1))
    (hQ : ContinuousOn Q (γ '' Icc 0 1)) :
    (∫ t in (0 : ℝ)..1,
      P ((γ ∘ endpointPauseClock) t) * (deriv (γ ∘ endpointPauseClock) t).re +
      Q ((γ ∘ endpointPauseClock) t) * (deriv (γ ∘ endpointPauseClock) t).im) =
      ∫ s in (0 : ℝ)..1, P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  have hFieldImage : MapsTo γ (endpointPauseClock '' Icc 0 1) (γ '' Icc 0 1) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨endpointPauseClock t, endpointPauseClock_mapsTo ht, rfl⟩
  simpa only [endpointPauseClock_zero, endpointPauseClock_one] using
    complex_line_integral_reparam γ endpointPauseClock (by norm_num : (0 : ℝ) ≤ 1)
      univ univ (γ '' Icc 0 1) isOpen_univ isOpen_univ
      hγ.contDiffOn endpointPauseClock_contDiff.contDiffOn
      (subset_univ _) (subset_univ _) hFieldImage P Q hP hQ

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.integral_local_clock
#check_upstream ClassicalTheorems.Progress.Green.deriv_comp_complex_local
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_reparam
#check_upstream ClassicalTheorems.Progress.Green.complex_winding_integral_reparam
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_reparametrized

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_reparametrized_of_positive_winding_at

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_reparametrized_abs

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_zero

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_one

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_contDiff

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_hasDerivAt

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_mapsTo

#check_upstream ClassicalTheorems.Progress.Green.deriv_endpointPauseClock_comp

#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_endpointPauseClock

#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_strictMonoOn
#check_upstream ClassicalTheorems.Progress.Green.endpointPauseClock_image

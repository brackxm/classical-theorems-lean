/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenPiecewiseClock

/-! Green's theorem for finite chains of C¹ pieces, with arbitrary corner
angles at their joins. Each original unit-interval line integral is preserved. -/

noncomputable section
open Set MeasureTheory
namespace ClassicalTheorems.Progress.Green

/-- Matching original endpoints identify the value at the next gluing point. -/
theorem pausedChain_join_value (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hMatch : ∀ i, i + 1 < n + 1 → γ i 1 = γ (i + 1) 0) :
    pausedChain γ n n = shiftedPausePiece (γ n) n n := by
  rw [shiftedPausePiece_start]
  cases n with
  | zero => rfl
  | succ k => simpa only [Nat.cast_add, Nat.cast_one] using
      (pausedChain_finish γ k).trans (hMatch k (by omega))

/-- The image of the finite chain is the union of its original piece images,
including its initial point in the zero-piece case. -/
theorem pausedChain_image_with_start (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0) :
    pausedChain γ n '' Icc 0 n = {γ 0 0} ∪ ⋃ i < n, γ i '' Icc 0 1 := by
  induction n with
  | zero => simp [pausedChain]
  | succ n ih =>
      rw [pausedChain, Nat.cast_add, Nat.cast_one,
        joinAt_image_Icc _ _ (Nat.cast_nonneg n) (by linarith)
          (pausedChain_join_value γ n hMatch), shiftedPausePiece_image,
        ih (fun i hi => hMatch i (by omega)), biUnion_lt_succ, union_assoc]

/-- A nonempty finite chain preserves precisely the original boundary image. -/
theorem pausedChain_image (γ : ℕ → ℝ → ℂ) {n : ℕ} (hn : 0 < n)
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0) :
    pausedChain γ n '' Icc 0 n = ⋃ i < n, γ i '' Icc 0 1 := by
  rw [pausedChain_image_with_start γ n hMatch]
  apply union_eq_right.mpr
  intro z hz
  rw [mem_singleton_iff] at hz
  subst z
  exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨hn, ⟨0, by norm_num, rfl⟩⟩⟩

/-- A shifted, flattened piece has exactly the line integral of its original
unit piece, including when the original endpoint tangent is nonzero. -/
theorem complex_line_integral_shiftedPausePiece (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (n : ℕ) (P Q : ℂ → ℝ) (hP : ContinuousOn P (γ '' Icc 0 1))
    (hQ : ContinuousOn Q (γ '' Icc 0 1)) :
    (∫ t in (n : ℝ)..(n + 1),
      P (shiftedPausePiece γ n t) * (deriv (shiftedPausePiece γ n) t).re +
      Q (shiftedPausePiece γ n t) * (deriv (shiftedPausePiece γ n) t).im) =
      ∫ s in (0 : ℝ)..1, P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  let φ : ℝ → ℝ := fun t => endpointPauseClock (t - n)
  have he : shiftedPausePiece γ n = γ ∘ φ := by funext t; rfl
  have hφ : ContDiff ℝ 1 φ := endpointPauseClock_contDiff.comp (contDiff_id.sub contDiff_const)
  have hImage : MapsTo γ (φ '' Icc (n : ℝ) (n + 1)) (γ '' Icc 0 1) := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨φ t, endpointPauseClock_mapsTo ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  have hs : φ n = 0 := by simp [φ]
  have hf : φ (n + 1) = 1 := by simp [φ]
  rw [he]
  simpa only [hs, hf] using complex_line_integral_reparam γ φ (by linarith : (n : ℝ) ≤ n + 1)
    univ univ (γ '' Icc 0 1) isOpen_univ isOpen_univ hγ.contDiffOn hφ.contDiffOn
    (subset_univ _) (subset_univ _) hImage P Q hP hQ

/-- Integrability on an arbitrary compact parameter interval. -/
theorem complex_line_integrable_interval (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (U : Set ℂ) {a b : ℝ} (hab : a ≤ b) (hImage : MapsTo γ (Icc a b) U)
    (P Q : ℂ → ℝ) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) :
    IntervalIntegrable (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im)
      volume a b := by
  have hd := hγ.continuous_deriv_one
  exact (((hP.comp hγ.continuous.continuousOn hImage).mul
    (Complex.continuous_re.comp hd).continuousOn).add
    ((hQ.comp hγ.continuous.continuousOn hImage).mul
      (Complex.continuous_im.comp hd).continuousOn)).intervalIntegrable_of_Icc hab

/-- Gluing compatible C¹ branches adds their line integrals. Endpoints are
included because the branch derivatives agree there. -/
theorem complex_line_integral_joinAt (f g : ℝ → ℂ) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (he : f c = g c) (hd : deriv f c = deriv g c) (U : Set ℂ)
    (hImage : MapsTo (joinAt c f g) (Icc a b) U)
    (P Q : ℂ → ℝ) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) :
    (∫ t in a..b, P (joinAt c f g t) * (deriv (joinAt c f g) t).re +
      Q (joinAt c f g t) * (deriv (joinAt c f g) t).im) =
      (∫ t in a..c, P (f t) * (deriv f t).re + Q (f t) * (deriv f t).im) +
      ∫ t in c..b, P (g t) * (deriv g t).re + Q (g t) * (deriv g t).im := by
  have hi := complex_line_integrable_interval (joinAt c f g)
    (joinAt_contDiff c f g hf hg he hd) U (hac.trans hcb) hImage P Q hP hQ
  have hil := hi.mono_set (by
    rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc le_rfl hcb)
  have hir := hi.mono_set (by
    rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc hac le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hil hir]
  congr 1
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hac] at ht
    dsimp only
    rw [joinAt_deriv c f g hf hg he hd]
    simp only [joinAt, ite_eq_left ht.2]
  · apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hcb] at ht
    dsimp only
    rw [joinAt_deriv c f g hf hg he hd]
    by_cases htc : t ≤ c
    · have htc' : t = c := le_antisymm htc ht.1
      simp only [htc', joinAt, le_refl, ite_true, he, hd]
    · simp only [joinAt, ite_eq_right htc]

/-- The line integral of the finite C¹ chain equals the finite sum of the
original pieces, with no tangent-matching requirement on those original pieces. -/
theorem complex_line_integral_pausedChain (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0)
    (U : Set ℂ) (hStart : γ 0 0 ∈ U) (hImage : ∀ i < n, MapsTo (γ i) (Icc 0 1) U)
    (P Q : ℂ → ℝ) (hP : ContinuousOn P U) (hQ : ContinuousOn Q U) :
    (∫ t in (0 : ℝ)..n,
      P (pausedChain γ n t) * (deriv (pausedChain γ n) t).re +
      Q (pausedChain γ n t) * (deriv (pausedChain γ n) t).im) =
      ∑ i ∈ Finset.range n, ∫ s in (0 : ℝ)..1,
        P (γ i s) * (deriv (γ i) s).re + Q (γ i s) * (deriv (γ i) s).im := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨hPrev, hPrevEnd⟩ := pausedChain_contDiff_and_deriv_end γ n
        (fun i hi => hγ i (by omega)) (fun i hi => hMatch i (by omega))
      have hNext := shiftedPausePiece_contDiff (γ n) (hγ n (by omega)) n
      have hNextStart := (shiftedPausePiece_deriv_endpoints (γ n) (hγ n (by omega)) n).1
      have hAllImage := pausedChain_mapsTo γ (n + 1) U hStart hImage
      rw [pausedChain, Nat.cast_add, Nat.cast_one]
      rw [complex_line_integral_joinAt _ _ (Nat.cast_nonneg n) (by linarith)
        hPrev hNext (pausedChain_join_value γ n hMatch) (hPrevEnd.trans hNextStart.symm)
        U (by simpa only [pausedChain, Nat.cast_add, Nat.cast_one] using hAllImage)
        P Q hP hQ]
      rw [ih (fun i hi => hγ i (by omega)) (fun i hi => hMatch i (by omega))
        (fun i hi => hImage i (by omega)),
        complex_line_integral_shiftedPausePiece (γ n) (hγ n (by omega)) n P Q
          (hP.mono (image_subset_iff.mpr (hImage n (by omega))))
          (hQ.mono (image_subset_iff.mpr (hImage n (by omega)))), Finset.sum_range_succ]

/-- Signed Green for a closed simple finite chain of C¹ pieces, with arbitrary
corners between pieces. Simplicity is assumed for the original concatenation;
one automatically derived orientation sign works for every coefficient pair. -/
theorem greens_theorem_piecewise (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n + 1, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n + 1 → γ i 1 = γ (i + 1) 0)
    (hClosed : γ n 1 = γ 0 0) (hSimple : InjOn (rawChain γ (n + 1)) (Ico (0 : ℝ) (n + 1 : ℕ)))
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = ⋃ i < n + 1, γ i '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U) :
    ∃ orientation : Bool,
      (∀ z ∈ D, (∫ t in (0 : ℝ)..(n + 1 : ℕ),
        (deriv (pausedChain γ (n + 1)) t / (pausedChain γ (n + 1) t - z)).im) =
          if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        (∑ i ∈ Finset.range (n + 1), ∫ s in (0 : ℝ)..1,
          P (γ i s) * (deriv (γ i) s).re + Q (γ i s) * (deriv (γ i) s).im) =
          (if orientation then 1 else -1) *
            ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  have hCurve := (pausedChain_contDiff_and_deriv_end γ (n + 1) hγ hMatch).1
  have hb : frontier D = pausedChain γ (n + 1) '' Icc (0 : ℝ) (n + 1 : ℕ) :=
    hBoundary.trans (pausedChain_image γ (Nat.succ_pos n) hMatch).symm
  have hc : pausedChain γ (n + 1) 0 = pausedChain γ (n + 1) (n + 1 : ℕ) := by
    rw [pausedChain_start]
    simpa only [Nat.cast_add, Nat.cast_one] using ((pausedChain_finish γ n).trans hClosed).symm
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_interval D U (pausedChain γ (n + 1))
    (by exact_mod_cast Nat.succ_pos n) hDomain hBounded hConnected hb hOpen hNeighborhood
    hCurve hc (pausedChain_injOn_of_rawChain γ (n + 1) hSimple)
  have hImages : ∀ i < n + 1, MapsTo (γ i) (Icc 0 1) U := by
    intro i hi s hs
    apply hNeighborhood
    apply frontier_subset_closure
    rw [hBoundary]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ⟨s, hs, rfl⟩⟩⟩
  have hStart : γ 0 0 ∈ U := hImages 0 (Nat.succ_pos n) (by norm_num)
  refine ⟨orientation, hw, fun P Q hP hQ => ?_⟩
  rw [← complex_line_integral_pausedChain γ (n + 1) hγ hMatch U hStart hImages P Q
    hP.continuousOn hQ.continuousOn]
  exact hg P Q hP hQ

/-- A positive winding check at one domain point fixes the sign for the
piecewise Green formula. The check uses the constructed C¹ parametrization. -/
theorem greens_theorem_piecewise_of_positive_winding_at (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n + 1, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n + 1 → γ i 1 = γ (i + 1) 0)
    (hClosed : γ n 1 = γ 0 0) (hSimple : InjOn (rawChain γ (n + 1)) (Ico (0 : ℝ) (n + 1 : ℕ)))
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = ⋃ i < n + 1, γ i '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U) (z : ℂ) (hz : z ∈ D)
    (hPositive : (∫ t in (0 : ℝ)..(n + 1 : ℕ),
      (deriv (pausedChain γ (n + 1)) t / (pausedChain γ (n + 1) t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∑ i ∈ Finset.range (n + 1), ∫ s in (0 : ℝ)..1,
      P (γ i s) * (deriv (γ i) s).re + Q (γ i s) * (deriv (γ i) s).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_piecewise D U γ n hγ hMatch hClosed hSimple
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Green's magnitude identity for a finite simple piecewise C¹ boundary,
with no orientation or tangent-matching hypothesis. -/
theorem greens_theorem_piecewise_abs (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n + 1, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n + 1 → γ i 1 = γ (i + 1) 0)
    (hClosed : γ n 1 = γ 0 0) (hSimple : InjOn (rawChain γ (n + 1)) (Ico (0 : ℝ) (n + 1 : ℕ)))
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = ⋃ i < n + 1, γ i '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∑ i ∈ Finset.range (n + 1), ∫ s in (0 : ℝ)..1,
      P (γ i s) * (deriv (γ i) s).re + Q (γ i s) * (deriv (γ i) s).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_piecewise D U γ n hγ hMatch hClosed hSimple
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.pausedChain_join_value
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_image_with_start
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_image
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_shiftedPausePiece
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integrable_interval
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_joinAt
#check_upstream ClassicalTheorems.Progress.Green.complex_line_integral_pausedChain

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise_of_positive_winding_at
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise_abs

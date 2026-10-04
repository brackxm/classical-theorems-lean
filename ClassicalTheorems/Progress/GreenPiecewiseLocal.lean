/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenPiecewise

/-! Green's theorem for finite chains whose pieces are C¹ only near their own
unit intervals. Compact extensions preserve the original boundary and integrals. -/

noncomputable section
open Set MeasureTheory
namespace ClassicalTheorems.Progress.Green

/-- Choose global C¹ representatives agreeing with each used piece on an open
neighborhood of its interval. Unused pieces require no regularity assumption. -/
theorem exists_c1_piece_extensions (γ : ℕ → ℝ → ℂ) (n : ℕ) (V : ℕ → Set ℝ)
    (hV : ∀ i < n, IsOpen (V i)) (hInterval : ∀ i < n, Icc (0 : ℝ) 1 ⊆ V i)
    (hγ : ∀ i < n, ContDiffOn ℝ 1 (γ i) (V i)) :
    ∃ (δ : ℕ → ℝ → ℂ) (W : ℕ → Set ℝ), ∀ i < n,
      ContDiff ℝ 1 (δ i) ∧ IsOpen (W i) ∧ Icc (0 : ℝ) 1 ⊆ W i ∧ EqOn (δ i) (γ i) (W i) := by
  have hx : ∀ i : ℕ, ∃ (δ : ℝ → ℂ) (W : Set ℝ), i < n →
      ContDiff ℝ 1 δ ∧ IsOpen W ∧ Icc (0 : ℝ) 1 ⊆ W ∧ EqOn δ (γ i) W := by
    intro i
    by_cases hi : i < n
    · obtain ⟨δ, W, hd, _, hw, hiw, he⟩ := exists_compactSupport_extension_vector
        (Icc (0 : ℝ) 1) (V i) isCompact_Icc (hV i hi) (hInterval i hi) (γ i) (hγ i hi)
      exact ⟨δ, W, fun _ => ⟨hd, hw, hiw, he⟩⟩
    · exact ⟨fun _ => 0, ∅, fun h => (hi h).elim⟩
  choose δ W h using hx
  exact ⟨δ, W, h⟩

/-- Agreement on all used unit intervals preserves the original concatenation. -/
theorem rawChain_eqOn_of_piece_eqOn (γ δ : ℕ → ℝ → ℂ) (n : ℕ)
    (hStart : δ 0 0 = γ 0 0) (he : ∀ i < n, EqOn (δ i) (γ i) (Icc (0 : ℝ) 1)) :
    EqOn (rawChain δ n) (rawChain γ n) (Icc (0 : ℝ) n) := by
  induction n with
  | zero => intro t ht; simpa only [rawChain] using hStart
  | succ n ih =>
      intro t ht
      have ht' : t ≤ (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using ht.2
      by_cases htn : t ≤ n
      · simpa only [rawChain, joinAt, ite_eq_left htn] using
          ih (fun i hi => he i (by omega)) ⟨ht.1, htn⟩
      · simpa only [rawChain, joinAt, ite_eq_right htn] using
          he n (by omega) ⟨by linarith, by linarith⟩

/-- Open-neighborhood agreement survives endpoint flattening, including at
joins. Consequently the actual derivatives of both paused chains agree. -/
theorem pausedChain_eventuallyEq_of_piece_eventuallyEq (γ δ : ℕ → ℝ → ℂ) (n : ℕ)
    (hStart : δ 0 0 = γ 0 0)
    (he : ∀ i < n, ∀ s ∈ Icc (0 : ℝ) 1, δ i =ᶠ[nhds s] γ i) :
    ∀ t ∈ Icc (0 : ℝ) n, pausedChain δ n =ᶠ[nhds t] pausedChain γ n := by
  induction n with
  | zero => intro t ht; simp only [pausedChain, hStart]; rfl
  | succ n ih =>
      intro t ht
      have ht' : t ≤ (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using ht.2
      have hNext (h : (n : ℝ) ≤ t) :
          shiftedPausePiece (δ n) n =ᶠ[nhds t] shiftedPausePiece (γ n) n := by
        have hs : endpointPauseClock (t - n) ∈ Icc (0 : ℝ) 1 :=
          endpointPauseClock_mapsTo ⟨by linarith, by linarith⟩
        exact (he n (by omega) _ hs).comp_tendsto
          ((endpointPauseClock_contDiff.continuous.comp (continuous_id.sub continuous_const)).tendsto t)
      rw [pausedChain, pausedChain]
      rcases lt_trichotomy t (n : ℝ) with htn | rfl | htn
      · exact (joinAt_eventually_left _ _ _ htn).trans
          ((ih (fun i hi => he i (by omega)) t ⟨ht.1, htn.le⟩).trans
            (joinAt_eventually_left _ _ _ htn).symm)
      · filter_upwards [ih (fun i hi => he i (by omega)) n ⟨Nat.cast_nonneg n, le_rfl⟩,
          hNext le_rfl] with s hs hn
        simp only [joinAt]
        split_ifs <;> assumption
      · exact (joinAt_eventually_right _ _ _ htn).trans
          ((hNext htn.le).trans (joinAt_eventually_right _ _ _ htn).symm)

/-- Signed Green for a closed simple finite chain of locally C¹ pieces, with arbitrary
corners between pieces. Each piece is C¹ only on its own open neighborhood
of [0,1]. Simplicity is assumed for the original concatenation;
one automatically derived orientation sign works for every coefficient pair. -/
theorem greens_theorem_piecewise_local (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (V : ℕ → Set ℝ) (hV : ∀ i < n + 1, IsOpen (V i))
    (hInterval : ∀ i < n + 1, Icc (0 : ℝ) 1 ⊆ V i)
    (hγ : ∀ i < n + 1, ContDiffOn ℝ 1 (γ i) (V i))
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
  obtain ⟨δ, W, hδ⟩ := exists_c1_piece_extensions γ (n + 1) V hV hInterval hγ
  have he : ∀ i < n + 1, EqOn (δ i) (γ i) (Icc (0 : ℝ) 1) :=
    fun i hi => (hδ i hi).2.2.2.mono (hδ i hi).2.2.1
  have hEvent : ∀ i < n + 1, ∀ s ∈ Icc (0 : ℝ) 1, δ i =ᶠ[nhds s] γ i := by
    intro i hi s hs
    exact Filter.mem_of_superset ((hδ i hi).2.1.mem_nhds ((hδ i hi).2.2.1 hs))
      (fun t ht => (hδ i hi).2.2.2 ht)
  have hd : ∀ i < n + 1, EqOn (deriv (δ i)) (deriv (γ i)) (Icc (0 : ℝ) 1) :=
    fun i hi s hs => (hEvent i hi s hs).deriv_eq
  have hStart : δ 0 0 = γ 0 0 := he 0 (Nat.succ_pos n) (by norm_num)
  have hMatchδ : ∀ i, i + 1 < n + 1 → δ i 1 = δ (i + 1) 0 := by
    intro i hi
    rw [he i (by omega) (by norm_num), he (i + 1) hi (by norm_num), hMatch i hi]
  have hClosedδ : δ n 1 = δ 0 0 := by
    rw [he n (by omega) (by norm_num), hStart, hClosed]
  have hSimpleδ : InjOn (rawChain δ (n + 1)) (Ico (0 : ℝ) (n + 1 : ℕ)) :=
    ((rawChain_eqOn_of_piece_eqOn γ δ (n + 1) hStart he).mono Ico_subset_Icc_self).injOn_iff.mpr hSimple
  have hBoundaryδ : frontier D = ⋃ i < n + 1, δ i '' Icc 0 1 := by
    rw [hBoundary]
    apply iUnion_congr
    intro i
    apply iUnion_congr
    intro hi
    exact (he i hi).image_eq.symm
  have hChainEvent := pausedChain_eventuallyEq_of_piece_eventuallyEq γ δ (n + 1) hStart hEvent
  have hChain : EqOn (pausedChain δ (n + 1)) (pausedChain γ (n + 1))
      (Icc (0 : ℝ) (n + 1 : ℕ)) := fun t ht => (hChainEvent t ht).eq_of_nhds
  have hChainDeriv : EqOn (deriv (pausedChain δ (n + 1))) (deriv (pausedChain γ (n + 1)))
      (Icc (0 : ℝ) (n + 1 : ℕ)) := fun t ht => (hChainEvent t ht).deriv_eq
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_piecewise D U δ n
    (fun i hi => (hδ i hi).1) hMatchδ hClosedδ hSimpleδ hDomain hBounded hConnected
    hBoundaryδ hOpen hNeighborhood
  refine ⟨orientation, fun z hz => ?_, fun P Q hP hQ => ?_⟩
  · rw [← complex_winding_integral_eq_of_eqOn (pausedChain γ (n + 1))
      (pausedChain δ (n + 1)) (Nat.cast_nonneg _) hChain hChainDeriv z]
    exact hw z hz
  · rw [← hg P Q hP hQ]
    apply Finset.sum_congr rfl
    intro i hi
    exact (complex_line_integral_eq_of_eqOn (γ i) (δ i) (by norm_num)
      (he i (Finset.mem_range.mp hi)) (hd i (Finset.mem_range.mp hi)) P Q).symm

/-- A positive winding check at one domain point fixes the sign for the
locally C¹ piecewise Green formula. The check uses the constructed C¹ parametrization. -/
theorem greens_theorem_piecewise_local_of_positive_winding_at (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (V : ℕ → Set ℝ) (hV : ∀ i < n + 1, IsOpen (V i))
    (hInterval : ∀ i < n + 1, Icc (0 : ℝ) 1 ⊆ V i)
    (hγ : ∀ i < n + 1, ContDiffOn ℝ 1 (γ i) (V i))
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
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_piecewise_local D U γ n V hV hInterval hγ hMatch hClosed hSimple
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Green's magnitude identity for a finite simple boundary of locally C¹ pieces,
with no orientation or tangent-matching hypothesis. -/
theorem greens_theorem_piecewise_local_abs (D U : Set ℂ) (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (V : ℕ → Set ℝ) (hV : ∀ i < n + 1, IsOpen (V i))
    (hInterval : ∀ i < n + 1, Icc (0 : ℝ) 1 ⊆ V i)
    (hγ : ∀ i < n + 1, ContDiffOn ℝ 1 (γ i) (V i))
    (hMatch : ∀ i, i + 1 < n + 1 → γ i 1 = γ (i + 1) 0)
    (hClosed : γ n 1 = γ 0 0) (hSimple : InjOn (rawChain γ (n + 1)) (Ico (0 : ℝ) (n + 1 : ℕ)))
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = ⋃ i < n + 1, γ i '' Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |∑ i ∈ Finset.range (n + 1), ∫ s in (0 : ℝ)..1,
      P (γ i s) * (deriv (γ i) s).re + Q (γ i s) * (deriv (γ i) s).im| =
      |∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_piecewise_local D U γ n V hV hInterval hγ hMatch hClosed hSimple
    hDomain hBounded hConnected hBoundary hOpen hNeighborhood
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.exists_c1_piece_extensions
#check_upstream ClassicalTheorems.Progress.Green.rawChain_eqOn_of_piece_eqOn
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_eventuallyEq_of_piece_eventuallyEq

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local_of_positive_winding_at

#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local_abs

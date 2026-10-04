/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenGluing

/-! The flattened finite chain is a reparametrization of the original piecewise
curve by a continuous, strictly increasing clock. Simplicity is preserved. -/

noncomputable section
open Set
namespace ClassicalTheorems.Progress.Green

/-- The original concatenation, with each piece on one unit interval. -/
def rawChain (γ : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => γ 0 0
  | n + 1 => joinAt n (rawChain γ n) (fun t => γ n (t - n))

/-- Apply the endpoint-pause clock separately on each unit interval. -/
def piecewisePauseClock : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => joinAt n (piecewisePauseClock n)
      (fun t => n + endpointPauseClock (t - n))

@[simp] theorem piecewisePauseClock_start (n : ℕ) : piecewisePauseClock n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [piecewisePauseClock, joinAt] using ih

/-- The finite clock preserves its last endpoint. -/
theorem piecewisePauseClock_finish (n : ℕ) : piecewisePauseClock n n = n := by
  cases n with
  | zero => simp [piecewisePauseClock]
  | succ n =>
      rw [piecewisePauseClock, joinAt,
        ite_eq_right (by exact_mod_cast Nat.not_succ_le_self n)]
      simp [Nat.cast_add, Nat.cast_one]

/-- A compatible join of increasing branches remains increasing. -/
theorem joinAt_strictMonoOn (f g : ℝ → ℝ) {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hf : StrictMonoOn f (Icc a c)) (hg : StrictMonoOn g (Icc c b))
    (he : f c = g c) : StrictMonoOn (joinAt c f g) (Icc a b) := by
  intro s hs t ht hst
  by_cases hsc : s ≤ c
  · by_cases htc : t ≤ c
    · simp only [joinAt, ite_eq_left hsc, ite_eq_left htc]
      exact hf ⟨hs.1, hsc⟩ ⟨ht.1, htc⟩ hst
    · simp only [joinAt, ite_eq_left hsc, ite_eq_right htc]
      have hl : f s ≤ f c := hf.monotoneOn ⟨hs.1, hsc⟩ ⟨hac, le_rfl⟩ hsc
      have hr : g c < g t := hg ⟨le_rfl, hcb⟩ ⟨(not_le.mp htc).le, ht.2⟩ (not_le.mp htc)
      exact hl.trans_lt (he ▸ hr)
  · have htc : ¬t ≤ c := by linarith [not_le.mp hsc]
    simp only [joinAt, ite_eq_right hsc, ite_eq_right htc]
    exact hg ⟨(not_le.mp hsc).le, hs.2⟩ ⟨(not_le.mp htc).le, ht.2⟩ hst

/-- The piecewise clock is continuous, including at all joins. -/
theorem piecewisePauseClock_continuous (n : ℕ) : Continuous (piecewisePauseClock n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      rw [piecewisePauseClock]
      apply ih.if _ (continuous_const.add
        (endpointPauseClock_contDiff.continuous.comp (continuous_id.sub continuous_const)))
      intro t ht
      have htn : t = (n : ℝ) := by
        simpa only [show {t : ℝ | t ≤ (n : ℝ)} = Iic (n : ℝ) from rfl,
          frontier_Iic, mem_singleton_iff] using ht
      subst t
      simp [piecewisePauseClock_finish]

/-- Endpoint flattening preserves the order of all parameters, including joins. -/
theorem piecewisePauseClock_strictMonoOn (n : ℕ) :
    StrictMonoOn (piecewisePauseClock n) (Icc (0 : ℝ) n) := by
  induction n with
  | zero =>
      intro s hs t ht hst
      simp only [Nat.cast_zero] at hs ht
      have hs0 : s = 0 := le_antisymm hs.2 hs.1
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      simp [hs0, ht0] at hst
  | succ n ih =>
      rw [piecewisePauseClock, Nat.cast_add, Nat.cast_one]
      apply joinAt_strictMonoOn _ _ (Nat.cast_nonneg n) (by linarith) ih
      · intro s hs t ht hst
        dsimp only
        apply add_lt_add_right
        apply endpointPauseClock_strictMonoOn
        · exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
        · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · linarith
      · simp [piecewisePauseClock_finish]

/-- The finite clock covers the original parameter interval exactly. -/
theorem piecewisePauseClock_image (n : ℕ) :
    piecewisePauseClock n '' Icc (0 : ℝ) n = Icc (0 : ℝ) n := by
  simpa only [piecewisePauseClock_start, piecewisePauseClock_finish] using
    (piecewisePauseClock_continuous n).continuousOn.image_Icc_of_monotoneOn
      (Nat.cast_nonneg n) (piecewisePauseClock_strictMonoOn n).monotoneOn

/-- All visited parameters stay in the original compact interval. -/
theorem piecewisePauseClock_mapsTo (n : ℕ) :
    MapsTo (piecewisePauseClock n) (Icc (0 : ℝ) n) (Icc (0 : ℝ) n) := by
  intro t ht
  rw [← piecewisePauseClock_image n]
  exact mem_image_of_mem _ ht

/-- The terminal endpoint remains excluded for nonterminal input parameters. -/
theorem piecewisePauseClock_mapsTo_Ico (n : ℕ) :
    MapsTo (piecewisePauseClock n) (Ico (0 : ℝ) n) (Ico (0 : ℝ) n) := by
  intro t ht
  have hlo := (piecewisePauseClock_mapsTo n (Ico_subset_Icc_self ht)).1
  have hhi := piecewisePauseClock_strictMonoOn n (Ico_subset_Icc_self ht)
    ⟨Nat.cast_nonneg n, le_rfl⟩ ht.2
  exact ⟨hlo, by simpa only [piecewisePauseClock_finish] using hhi⟩

/-- The flattened chain traces the original chain through the finite clock. -/
theorem pausedChain_eq_rawChain_clock (γ : ℕ → ℝ → ℂ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) n) :
    pausedChain γ n t = rawChain γ n (piecewisePauseClock n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      by_cases htn : t ≤ n
      · have hprev := piecewisePauseClock_mapsTo n ⟨ht.1, htn⟩
        simpa only [pausedChain, piecewisePauseClock, rawChain, joinAt,
          ite_eq_left htn, ite_eq_left hprev.2] using ih ⟨ht.1, htn⟩
      · have hu : t - n ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [not_le.mp htn], by have h := ht.2; push_cast at h; linarith⟩
        have hp : 0 < endpointPauseClock (t - n) := by
          have h := endpointPauseClock_strictMonoOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
            hu (by linarith [not_le.mp htn])
          simpa only [endpointPauseClock_zero] using h
        simp only [pausedChain, piecewisePauseClock, rawChain, joinAt, ite_eq_right htn,
          ite_eq_right (by linarith : ¬(n : ℝ) + endpointPauseClock (t - n) ≤ n),
          shiftedPausePiece, add_sub_cancel_left]

/-- Simplicity of the original finite piecewise curve implies simplicity of its
C¹ flattened parametrization. No geometric assumption is added by slowing it. -/
theorem pausedChain_injOn_of_rawChain (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hSimple : InjOn (rawChain γ n) (Ico (0 : ℝ) n)) : InjOn (pausedChain γ n) (Ico (0 : ℝ) n) := by
  intro s hs t ht he
  rw [pausedChain_eq_rawChain_clock γ n (Ico_subset_Icc_self hs),
    pausedChain_eq_rawChain_clock γ n (Ico_subset_Icc_self ht)] at he
  have hclock := hSimple (piecewisePauseClock_mapsTo_Ico n hs)
    (piecewisePauseClock_mapsTo_Ico n ht) he
  exact (piecewisePauseClock_strictMonoOn n).injOn
    (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) hclock

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_start
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_finish
#check_upstream ClassicalTheorems.Progress.Green.joinAt_strictMonoOn
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_continuous
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_strictMonoOn
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_image
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_mapsTo
#check_upstream ClassicalTheorems.Progress.Green.piecewisePauseClock_mapsTo_Ico
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_eq_rawChain_clock
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_injOn_of_rawChain

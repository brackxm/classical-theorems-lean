/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenReparametrization
import Mathlib.Topology.Piecewise
import Mathlib.Order.Monotone.Union

/-! C¹ gluing at matching values and derivatives, and finite chains of
endpoint-flattened curve pieces. -/

noncomputable section
open Set MeasureTheory
namespace ClassicalTheorems.Progress.Green

/-- Join two maps at a parameter, choosing the first at the common endpoint. -/
def joinAt {E : Type*} (c : ℝ) (f g : ℝ → E) (t : ℝ) : E :=
  if t ≤ c then f t else g t

/-- The joined map agrees with its left branch before the join. -/
theorem joinAt_eventually_left {E : Type*} (c : ℝ) (f g : ℝ → E) {t : ℝ}
    (ht : t < c) : joinAt c f g =ᶠ[nhds t] f := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  simp [joinAt, le_of_lt (mem_Iio.mp hs)]

/-- The joined map agrees with its right branch after the join. -/
theorem joinAt_eventually_right {E : Type*} (c : ℝ) (f g : ℝ → E) {t : ℝ}
    (ht : c < t) : joinAt c f g =ᶠ[nhds t] g := by
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  simp [joinAt, not_le.mpr (mem_Ioi.mp hs)]

/-- Equal derivatives and values give an actual two-sided derivative at the join. -/
theorem joinAt_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f g : ℝ → E) (v : E) (hf : HasDerivAt f v c)
    (hg : HasDerivAt g v c) (he : f c = g c) :
    HasDerivAt (joinAt c f g) v c := by
  have hl : HasDerivWithinAt (joinAt c f g) v (Iic c) c :=
    hf.hasDerivWithinAt.congr (fun t ht => by simp [joinAt, mem_Iic.mp ht]) (by simp [joinAt])
  have hr : HasDerivWithinAt (joinAt c f g) v (Ici c) c := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      by_cases htc : t ≤ c
      · have htc' : t = c := le_antisymm htc ht
        simpa [joinAt, htc'] using he
      · simp [joinAt, htc]
    · simpa [joinAt] using he
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hl.union hr

/-- C¹ branches with matching values and derivatives glue to a global C¹ map. -/
theorem joinAt_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f g : ℝ → E) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (he : f c = g c) (hd : deriv f c = deriv g c) :
    ContDiff ℝ 1 (joinAt c f g) := by
  have hjoin := joinAt_hasDerivAt c f g (deriv f c)
    (hf.differentiable one_ne_zero c).hasDerivAt
    (hd ▸ (hg.differentiable one_ne_zero c).hasDerivAt) he
  have hdEq : deriv (joinAt c f g) = joinAt c (deriv f) (deriv g) := by
    funext t
    rcases lt_trichotomy t c with ht | rfl | ht
    · rw [(joinAt_eventually_left c f g ht).deriv_eq]
      simp [joinAt, ht.le]
    · simp [joinAt, hjoin.deriv]
    · rw [(joinAt_eventually_right c f g ht).deriv_eq]
      simp [joinAt, not_le.mpr ht]
  rw [contDiff_one_iff_deriv]
  constructor
  · intro t
    rcases lt_trichotomy t c with ht | rfl | ht
    · exact ((hf.differentiable one_ne_zero t).hasDerivAt.congr_of_eventuallyEq
        (joinAt_eventually_left c f g ht)).differentiableAt
    · exact hjoin.differentiableAt
    · exact ((hg.differentiable one_ne_zero t).hasDerivAt.congr_of_eventuallyEq
        (joinAt_eventually_right c f g ht)).differentiableAt
  · rw [hdEq]
    apply hf.continuous_deriv_one.if _ hg.continuous_deriv_one
    intro t ht
    have htc : t = c := by simpa only [show {t : ℝ | t ≤ c} = Iic c from rfl,
      frontier_Iic, mem_singleton_iff] using ht
    simpa [htc] using hd

/-- An endpoint-flattened unit curve placed on [n,n+1]. -/
def shiftedPausePiece (γ : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  γ (endpointPauseClock (t - n))

@[simp] theorem shiftedPausePiece_start (γ : ℝ → ℂ) (n : ℕ) :
    shiftedPausePiece γ n n = γ 0 := by simp [shiftedPausePiece]

@[simp] theorem shiftedPausePiece_finish (γ : ℝ → ℂ) (n : ℕ) :
    shiftedPausePiece γ n ((n : ℝ) + 1) = γ 1 := by simp [shiftedPausePiece]

/-- Shifting a flattened piece preserves C¹ regularity. -/
theorem shiftedPausePiece_contDiff (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (n : ℕ) :
    ContDiff ℝ 1 (shiftedPausePiece γ n) :=
  hγ.comp (endpointPauseClock_contDiff.comp (contDiff_id.sub contDiff_const))

/-- Both derivatives of a shifted piece vanish at its endpoints. -/
theorem shiftedPausePiece_deriv_endpoints (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (n : ℕ) :
    deriv (shiftedPausePiece γ n) n = 0 ∧
      deriv (shiftedPausePiece γ n) ((n : ℝ) + 1) = 0 := by
  have hd (t : ℝ) : deriv (shiftedPausePiece γ n) t =
      deriv (γ ∘ endpointPauseClock) (t - n) := by
    have he : shiftedPausePiece γ n =
        ((γ ∘ endpointPauseClock) ∘ (fun s : ℝ => s - n)) := by
      funext s
      simp only [shiftedPausePiece, Function.comp_def]
    rw [he]
    have h := (((hγ.comp endpointPauseClock_contDiff).differentiable one_ne_zero
      (t - n)).hasDerivAt).scomp t ((hasDerivAt_id t).sub_const (n : ℝ))
    simpa only [Function.comp_def, id_eq, one_smul] using h.deriv
  obtain ⟨h0, h1⟩ := deriv_endpointPauseClock_comp γ hγ
  constructor
  · rw [hd, sub_self]
    exact h0
  · rw [hd, show (n : ℝ) + 1 - n = 1 by ring]
    exact h1

/-- Concatenate the first n unit pieces, slowing each to zero speed at its
endpoints. The zero-piece chain is constant at the first starting point. -/
def pausedChain (γ : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => γ 0 0
  | n + 1 => joinAt n (pausedChain γ n) (shiftedPausePiece (γ n) n)

@[simp] theorem pausedChain_start (γ : ℕ → ℝ → ℂ) (n : ℕ) :
    pausedChain γ n 0 = γ 0 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [pausedChain, joinAt] using ih

/-- A nonempty chain finishes at the endpoint of its last original piece. -/
theorem pausedChain_finish (γ : ℕ → ℝ → ℂ) (n : ℕ) :
    pausedChain γ (n + 1) (n + 1) = γ n 1 := by
  rw [pausedChain, joinAt, ite_eq_right (by exact_mod_cast Nat.not_succ_le_self n)]
  simpa only [Nat.cast_add, Nat.cast_one] using shiftedPausePiece_finish (γ n) n

/-- Matching original endpoints suffice to glue any finite number of C¹
pieces, regardless of their incoming and outgoing tangent vectors. The resulting
chain is globally C¹ and has zero derivative at its final endpoint. -/
theorem pausedChain_contDiff_and_deriv_end (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0) :
    ContDiff ℝ 1 (pausedChain γ n) ∧ deriv (pausedChain γ n) n = 0 := by
  induction n with
  | zero => exact ⟨contDiff_const, by simp [pausedChain]⟩
  | succ n ih =>
      obtain ⟨hPrev, hPrevZero⟩ := ih (fun i hi => hγ i (by omega))
        (fun i hi => hMatch i (by omega))
      have hNext := shiftedPausePiece_contDiff (γ n) (hγ n (by omega)) n
      obtain ⟨hNextStart, hNextEnd⟩ :=
        shiftedPausePiece_deriv_endpoints (γ n) (hγ n (by omega)) n
      have he : pausedChain γ n n = shiftedPausePiece (γ n) n n := by
        rw [shiftedPausePiece_start]
        cases n with
        | zero => rfl
        | succ k => simpa only [Nat.cast_add, Nat.cast_one] using
            (pausedChain_finish γ k).trans (hMatch k (by omega))
      have hSmooth : ContDiff ℝ 1 (pausedChain γ (n + 1)) :=
        joinAt_contDiff n (pausedChain γ n) (shiftedPausePiece (γ n) n)
          hPrev hNext he (hPrevZero.trans hNextStart.symm)
      refine ⟨hSmooth, ?_⟩
      rw [pausedChain, Nat.cast_add, Nat.cast_one]
      rw [(joinAt_eventually_right (n : ℝ) (pausedChain γ n)
        (shiftedPausePiece (γ n) n) (by exact_mod_cast Nat.lt_succ_self n)).deriv_eq]
      simpa only [Nat.cast_add, Nat.cast_one] using hNextEnd

/-- A finite flattened chain starts with zero derivative too. -/
theorem pausedChain_deriv_start (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hγ : ∀ i < n, ContDiff ℝ 1 (γ i))
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0) :
    deriv (pausedChain γ n) 0 = 0 := by
  induction n with
  | zero => simp [pausedChain]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        rw [pausedChain]
        simp only [Nat.cast_zero]
        apply HasDerivAt.deriv
        apply joinAt_hasDerivAt
        · exact hasDerivAt_const 0 _
        · have h := (shiftedPausePiece_contDiff (γ 0) (hγ 0 (by omega)) 0).differentiable
              one_ne_zero 0
          have hd := (shiftedPausePiece_deriv_endpoints (γ 0) (hγ 0 (by omega)) 0).1
          exact h.hasDerivAt.congr_deriv (by simpa only [Nat.cast_zero] using hd)
        · simp [pausedChain, shiftedPausePiece]
      · rw [pausedChain]
        rw [(joinAt_eventually_left (n : ℝ) (pausedChain γ n)
          (shiftedPausePiece (γ n) n) (by exact_mod_cast Nat.pos_of_ne_zero hn)).deriv_eq]
        exact ih (fun i hi => hγ i (by omega)) (fun i hi => hMatch i (by omega))

/-- Every point visited by a finite chain lies on one of the original pieces
(or its initial point in the zero-piece case). -/
theorem pausedChain_mapsTo (γ : ℕ → ℝ → ℂ) (n : ℕ) (U : Set ℂ)
    (hStart : γ 0 0 ∈ U) (hImage : ∀ i < n, MapsTo (γ i) (Icc 0 1) U) :
    MapsTo (pausedChain γ n) (Icc 0 n) U := by
  induction n with
  | zero => intro t _; exact hStart
  | succ n ih =>
      intro t ht
      change (if t ≤ (n : ℝ) then pausedChain γ n t else shiftedPausePiece (γ n) n t) ∈ U
      split_ifs with htn
      · exact ih (fun i hi => hImage i (by omega)) ⟨ht.1, htn⟩
      · apply hImage n (by omega)
        apply endpointPauseClock_mapsTo
        constructor
        · linarith [not_le.mp htn]
        · have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
          linarith [ht.2]

/-- The derivative of a compatible join is the join of the branch derivatives. -/
theorem joinAt_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (f g : ℝ → E) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (he : f c = g c) (hd : deriv f c = deriv g c) :
    deriv (joinAt c f g) = joinAt c (deriv f) (deriv g) := by
  have hjoin := joinAt_hasDerivAt c f g (deriv f c)
    (hf.differentiable one_ne_zero c).hasDerivAt
    (hd ▸ (hg.differentiable one_ne_zero c).hasDerivAt) he
  funext t
  rcases lt_trichotomy t c with ht | rfl | ht
  · rw [(joinAt_eventually_left c f g ht).deriv_eq]
    simp [joinAt, ht.le]
  · simp [joinAt, hjoin.deriv]
  · rw [(joinAt_eventually_right c f g ht).deriv_eq]
    simp [joinAt, not_le.mpr ht]

/-- Compatible joins preserve exactly the union of the two branch images. -/
theorem joinAt_image_Icc {E : Type*} (f g : ℝ → E) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (he : f c = g c) :
    joinAt c f g '' Icc a b = f '' Icc a c ∪ g '' Icc c b := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases htc : t ≤ c
    · exact Or.inl ⟨t, ⟨ht.1, htc⟩, by simp [joinAt, htc]⟩
    · exact Or.inr ⟨t, ⟨(not_le.mp htc).le, ht.2⟩, by simp [joinAt, htc]⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ⟨t, ⟨ht.1, ht.2.trans hcb⟩, by simp [joinAt, ht.2]⟩
    · refine ⟨t, ⟨hac.trans ht.1, ht.2⟩, ?_⟩
      by_cases htc : t ≤ c
      · have htc' : t = c := le_antisymm htc ht.1
        simpa [joinAt, htc'] using he
      · simp [joinAt, htc]

/-- Slowing and shifting a piece preserves its entire original image. -/
theorem shiftedPausePiece_image (γ : ℝ → ℂ) (n : ℕ) :
    shiftedPausePiece γ n '' Icc n ((n : ℝ) + 1) = γ '' Icc 0 1 := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨endpointPauseClock (t - n),
      endpointPauseClock_mapsTo ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨t, ht, hts⟩ := endpointPauseClock_image.symm ▸ hs
    refine ⟨n + t, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    simp only [shiftedPausePiece, add_sub_cancel_left, hts]

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.joinAt_eventually_left
#check_upstream ClassicalTheorems.Progress.Green.joinAt_eventually_right
#check_upstream ClassicalTheorems.Progress.Green.joinAt_hasDerivAt
#check_upstream ClassicalTheorems.Progress.Green.joinAt_contDiff
#check_upstream ClassicalTheorems.Progress.Green.shiftedPausePiece_start
#check_upstream ClassicalTheorems.Progress.Green.shiftedPausePiece_finish
#check_upstream ClassicalTheorems.Progress.Green.shiftedPausePiece_contDiff
#check_upstream ClassicalTheorems.Progress.Green.shiftedPausePiece_deriv_endpoints

#check_upstream ClassicalTheorems.Progress.Green.pausedChain_start
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_finish
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_contDiff_and_deriv_end
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_deriv_start
#check_upstream ClassicalTheorems.Progress.Green.pausedChain_mapsTo

#check_upstream ClassicalTheorems.Progress.Green.joinAt_deriv
#check_upstream ClassicalTheorems.Progress.Green.joinAt_image_Icc
#check_upstream ClassicalTheorems.Progress.Green.shiftedPausePiece_image

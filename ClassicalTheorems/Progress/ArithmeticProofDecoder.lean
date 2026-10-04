/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofTranslation
import ClassicalTheorems.Progress.ArithmeticEncoding

/-! A partial inverse of the exact-symbol Foundation translation. Positive
and negative forms are parsed together because Foundation stores formulas in
negation normal form. Accepted formulas recover the original syntax exactly. -/

noncomputable section
open Classical Encodable FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

def fromProofTerm {k : ℕ} : FFL.FirstOrder.ClosedSemiterm proofLanguage k →
    language.Term (Empty ⊕ Fin k)
  | .bvar i => .var (.inr i.rev)
  | .fvar a => Empty.elim a
  | .func f ts => .func f (fun i => fromProofTerm (ts i))

theorem fromProofTerm_to {k : ℕ} (t : language.Term (Empty ⊕ Fin k)) :
    fromProofTerm (toProofTerm t) = t := by
  induction t with
  | var a => cases a with
    | inl a => exact Empty.elim a
    | inr i => simp [fromProofTerm, toProofTerm]
  | func f ts ih => simp only [toProofTerm, fromProofTerm]; congr 1; funext i; exact ih i

theorem toProofTerm_from {k : ℕ} (t : FFL.FirstOrder.ClosedSemiterm proofLanguage k) :
    toProofTerm (fromProofTerm t) = t := by
  induction t with
  | bvar i => simp [fromProofTerm, toProofTerm]
  | fvar a => exact Empty.elim a
  | func f ts ih => simp only [toProofTerm, fromProofTerm]; congr 1; funext i; exact ih i

theorem proof_relation_arity {j : ℕ} (r : proofLanguage.Rel j) : j = 2 := by
  have h := r.isLt
  change r.val < (if j = 2 then 1 else 0) at h
  split_ifs at h <;> omega

theorem proof_relation_unique (r : proofLanguage.Rel 2) : r = proofEq := by
  apply Fin.ext
  have h := r.isLt
  change r.val < 1 at h
  change r.val = 0
  omega

def fromProofAtom {k j : ℕ} (r : proofLanguage.Rel j)
    (ts : Fin j → FFL.FirstOrder.ClosedSemiterm proofLanguage k) :
    language.BoundedFormula Empty k := by
  have h := proof_relation_arity r
  subst j
  exact .equal (fromProofTerm (ts 0)) (fromProofTerm (ts 1))

def fromProofFormula : {k : ℕ} → FFL.FirstOrder.Semisentence proofLanguage k →
    Option (language.BoundedFormula Empty k) × Option (language.BoundedFormula Empty k)
  | _, .verum => (none, some .falsum)
  | _, .falsum => (some .falsum, none)
  | _, .rel r ts => (some (fromProofAtom r ts), none)
  | _, .nrel r ts => (none, some (fromProofAtom r ts))
  | _, .and φ ψ => (none, (fromProofFormula φ).1.bind (fun p =>
      (fromProofFormula ψ).2.map (fun q => p.imp q)))
  | _, .or φ ψ => ((fromProofFormula φ).2.bind (fun p =>
      (fromProofFormula ψ).1.map (fun q => p.imp q)), none)
  | _, .all φ => ((fromProofFormula φ).1.map BoundedFormula.all, none)
  | _, .exs φ => (none, (fromProofFormula φ).2.map BoundedFormula.all)

theorem fromProofFormula_neg {k : ℕ} (φ : FFL.FirstOrder.Semisentence proofLanguage k) :
    fromProofFormula (∼φ) = ((fromProofFormula φ).2, (fromProofFormula φ).1) := by
  change fromProofFormula (FFL.FirstOrder.Semiformula.neg φ) = _
  induction φ <;> simp [fromProofFormula, FFL.FirstOrder.Semiformula.neg, *]

theorem fromProofAtom_to {k : ℕ} (t u : language.Term (Empty ⊕ Fin k)) :
    fromProofAtom proofEq ![toProofTerm t, toProofTerm u] = .equal t u := by
  simp [fromProofAtom, fromProofTerm_to]

theorem fromProofFormula_to {k : ℕ} (φ : language.BoundedFormula Empty k) :
    fromProofFormula (toProofFormula φ) = (some φ, none) := by
  induction φ with
  | falsum => rfl
  | equal t u => simp [toProofFormula, fromProofFormula, fromProofAtom_to]
  | rel r ts => cases r
  | imp φ ψ ihφ ihψ =>
    change ((fromProofFormula (∼toProofFormula φ)).2.bind (fun p =>
      (fromProofFormula (toProofFormula ψ)).1.map (fun q => p.imp q)), none) = _
    simp [fromProofFormula_neg, ihφ, ihψ]
  | all φ ih => simp [toProofFormula, fromProofFormula, ih]

theorem fromProofAtom_correct {k j : ℕ} (r : proofLanguage.Rel j)
    (ts : Fin j → FFL.FirstOrder.ClosedSemiterm proofLanguage k) :
    toProofFormula (fromProofAtom r ts) = .rel r ts := by
  have h := proof_relation_arity r
  subst j
  rw [proof_relation_unique r]
  simp only [fromProofAtom, toProofFormula, toProofTerm_from]
  congr 1
  exact (Matrix.fun_eq_vec_two ts).symm

theorem fromProofFormula_correct {k : ℕ} (σ : FFL.FirstOrder.Semisentence proofLanguage k) :
    (∀ φ, (fromProofFormula σ).1 = some φ → toProofFormula φ = σ) ∧
    (∀ φ, (fromProofFormula σ).2 = some φ → ∼toProofFormula φ = σ) := by
  induction σ with
  | verum => simp [fromProofFormula, toProofFormula]; rfl
  | falsum => simp [fromProofFormula, toProofFormula]; rfl
  | rel r ts => simp [fromProofFormula, fromProofAtom_correct]
  | nrel r ts => simp [fromProofFormula, fromProofAtom_correct]
  | and σ τ ihσ ihτ =>
    constructor
    · simp [fromProofFormula]
    · intro φ h
      simp only [fromProofFormula, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      have hσ := ihσ.1 p hp
      have hτ := ihτ.2 q hq
      change FFL.FirstOrder.Semiformula.and (∼(∼toProofFormula p)) (∼toProofFormula q) = _
      simp only [TildeInvolutive.tilde_involutive, hσ, hτ]
  | or σ τ ihσ ihτ =>
    constructor
    · intro φ h
      simp only [fromProofFormula, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, q, hq, rfl⟩ := h
      change FFL.FirstOrder.Semiformula.or (∼toProofFormula p) (toProofFormula q) = _
      rw [ihσ.2 p hp, ihτ.1 q hq]
    · simp [fromProofFormula]
  | all σ ih =>
    constructor
    · intro φ h
      simp only [fromProofFormula, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      simp [toProofFormula, ih.1 p hp]
    · simp [fromProofFormula]
  | exs σ ih =>
    constructor
    · simp [fromProofFormula]
    · intro φ h
      simp only [fromProofFormula, Option.map_eq_some_iff] at h
      obtain ⟨p, hp, rfl⟩ := h
      change FFL.FirstOrder.Semiformula.exs (∼toProofFormula p) = _
      rw [ih.2 p hp]

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.fromProofFormula_to
#check_upstream ClassicalTheorems.Progress.Arithmetic.fromProofFormula_correct

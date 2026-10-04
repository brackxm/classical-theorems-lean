/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofTranslation
import ClassicalTheorems.Progress.ArithmeticEffectiveSubstitution

/-! Effective translation of fixed formulas at numeral inputs. These proofs
compute Foundation's existing codes directly; the original syntax does not
need a new Primcodable instance. -/

noncomputable section
open Classical Encodable FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

local instance (j : ℕ) : Encodable (language.Functions j) :=
  FFL.FirstOrder.Language.Encodable.func (L := proofLanguage) j

theorem primrec_fixed_vecToNat {k : ℕ} (f : ℕ → Fin k → ℕ)
    (hf : ∀ i, Primrec (fun n => f n i)) :
    Primrec (fun n => Matrix.vecToNat (f n)) := by
  induction k with
  | zero => simpa [Matrix.vecToNat, Matrix.foldr] using (Primrec.const (0 : ℕ))
  | succ k ih =>
    have ht := ih (fun n i => f n i.succ) (fun i => hf i.succ)
    apply (Primrec.succ.comp (Primrec₂.natPair.comp (hf 0) ht)).of_eq
    intro n
    simp [Matrix.vecToNat, Matrix.foldr_succ, Matrix.vecHead, Matrix.vecTail]
    rfl

theorem primrec_proof_term_subst {α : Type*} {k : ℕ}
    (t : language.Term α) (tf : ℕ → α → language.Term (Empty ⊕ Fin k))
    (hf : ∀ a, Primrec (fun n => encode (toProofTerm (tf n a)))) :
    Primrec (fun n => encode (toProofTerm (t.subst (tf n)))) := by
  induction t with
  | var a => exact hf a
  | @func j f ts ih =>
    have ht := primrec_fixed_vecToNat
      (fun n i => encode (toProofTerm ((ts i).subst (tf n)))) ih
    have hp : Primrec (fun n => Nat.pair 2 (Nat.pair j (Nat.pair (encode (f : proofLanguage.Func j))
        (Matrix.vecToNat (fun i => encode (toProofTerm ((ts i).subst (tf n))))))) + 1) := by
      primrec
    exact hp

theorem primrec_proof_numeral_code {k : ℕ} :
    Primrec (fun n => encode (toProofTerm (numeralTerm n : language.Term (Empty ⊕ Fin k)))) := by
  let base := encode (toProofTerm (numeralTerm 0 : language.Term (Empty ⊕ Fin k)))
  let step := fun r : ℕ => Nat.pair 2 (Nat.pair 1 (Nat.pair 0 (Nat.pair r 0 + 1))) + 1
  have hs : Primrec₂ (fun _ r : ℕ => step r) := by dsimp [step]; primrec
  apply (Primrec.nat_rec₁ base hs).of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (Nat.rec base (fun _ r => step r) n) = _
    rw [ih]
    simp [step, numeralTerm, toProofTerm, FFL.FirstOrder.Semiterm.encode_eq_toNat,
      FFL.FirstOrder.Semiterm.toNat, Matrix.vecToNat, Matrix.foldr]
    rfl

theorem primrec_proof_formula_instances {k : ℕ}
    (φ : language.BoundedFormula ℕ k) (env : ℕ → ℕ → ℕ)
    (henv : ∀ i, Primrec (fun n => env n i)) :
    Primrec (fun n => encode (toProofFormula (φ.subst
      (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty k))) ∧
    Primrec (fun n => encode (∼toProofFormula (φ.subst
      (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty k))) := by
  induction φ with
  | falsum => exact ⟨Primrec.const _, Primrec.const _⟩
  | @equal k t u =>
    let tf : ℕ → ℕ ⊕ Fin k → language.Term (Empty ⊕ Fin k) :=
      fun n => Sum.elim (fun i => (numeralTerm (env n i) : language.Term Empty).relabel Sum.inl)
        (Term.var ∘ Sum.inr)
    have hf (a : ℕ ⊕ Fin k) : Primrec (fun n => encode (toProofTerm (tf n a))) := by
      cases a with
      | inl i => simpa only [tf, Sum.elim_inl, numeralTerm_relabel] using
          primrec_proof_numeral_code.comp (henv i)
      | inr i => exact Primrec.const _
    have ht := primrec_proof_term_subst t tf hf
    have hu := primrec_proof_term_subst u tf hf
    have hv := primrec_fixed_vecToNat (fun n =>
      ![encode (toProofTerm (t.subst (tf n))), encode (toProofTerm (u.subst (tf n)))])
      (by intro i; fin_cases i; exact ht; exact hu)
    have hv' : Primrec (fun n => Matrix.vecToNat (fun i =>
        encode (![toProofTerm (t.subst (tf n)), toProofTerm (u.subst (tf n))] i))) := by
      apply hv.of_eq
      intro n
      congr 1
      funext i
      fin_cases i <;> rfl
    have hp (tag : ℕ) : Primrec (fun n => Nat.pair tag (Nat.pair 2 (Nat.pair
        (encode proofEq) (Matrix.vecToNat (fun i =>
          encode (![toProofTerm (t.subst (tf n)), toProofTerm (u.subst (tf n))] i))))) + 1) := by
      primrec
    exact ⟨hp 0, hp 1⟩
  | rel r ts => cases r
  | imp φ ψ ihφ ihψ =>
    constructor
    · have hp : Primrec (fun n => Nat.pair 5 (Nat.pair
          (encode (∼toProofFormula ((φ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _))))
          (encode (toProofFormula ((ψ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _))))) + 1) := by
        have hφ := ihφ.2
        have hψ := ihψ.1
        primrec
      exact hp
    · have hp : Primrec (fun n => Nat.pair 4 (Nat.pair
          (encode (toProofFormula ((φ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _))))
          (encode (∼toProofFormula ((ψ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _))))) + 1) := by
        have hφ := ihφ.1
        have hψ := ihψ.2
        primrec
      apply hp.of_eq
      intro n
      change _ = encode (FFL.FirstOrder.Semiformula.and
        (FFL.FirstOrder.Semiformula.neg (FFL.FirstOrder.Semiformula.neg _)) _)
      rw [FFL.FirstOrder.Semiformula.neg_neg]
      rfl
  | all φ ih =>
    constructor
    · have h := ih.1
      apply (show Primrec (fun n => Nat.pair 6 (encode (toProofFormula
        ((φ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _)))) + 1) from by primrec).of_eq
      intro n
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, toProofFormula, id_eq]
      rfl
    · have h := ih.2
      apply (show Primrec (fun n => Nat.pair 7 (encode (∼toProofFormula
        ((φ.subst (fun i => numeralTerm (env n i)) : language.BoundedFormula Empty _)))) + 1) from by primrec).of_eq
      intro n
      simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, toProofFormula, id_eq]
      rfl

theorem primrec_proof_numeral_instances (φ : language.Formula ℕ) (env : ℕ → ℕ → ℕ)
    (henv : ∀ i, Primrec (fun n => env n i)) :
    Primrec (fun n => toProofSentence (numeralInstance φ (env n))) :=
  Primrec.encode_iff.mp (primrec_proof_formula_instances φ env henv).1

theorem primrec_program_env (i : ℕ) : Primrec (fun n => programEnv n i) := by
  by_cases hi : i = 0
  · apply Primrec.id.of_eq
    intro n
    simp [programEnv, hi]
  · simpa [programEnv, hi] using (Primrec.const (0 : ℕ))

theorem primrec_toProof_programSentence : Primrec (fun n => toProofSentence (programSentence n)) :=
  primrec_proof_numeral_instances _ programEnv primrec_program_env

theorem primrec_toProof_programSentence_not :
    Primrec (fun n => toProofSentence (programSentence n).not) :=
  primrec_proof_numeral_instances
    (rosserFormula 1 2 programWitnesses.positive programWitnesses.negative).not
    programEnv primrec_program_env

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_proof_numeral_code
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_proof_numeral_instances
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_toProof_programSentence
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_toProof_programSentence_not

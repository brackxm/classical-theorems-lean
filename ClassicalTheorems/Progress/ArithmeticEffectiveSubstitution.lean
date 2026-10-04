/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonProgramWitnesses
import Mathlib.Computability.Primrec.List

/-! Effectiveness of numeral substitution in the exact sentence encoding fixed
by the Robinson-Q theorem. We compute serialized tokens as natural-number lists,
preserving the exact encoding without assuming mathlib `Primcodable` instances. -/

noncomputable section
open Classical Encodable
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

theorem encode_list_map_encode {α : Type*} [Encodable α] (l : List α) :
    encode (l.map encode) = encode l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, encode_list_cons, ih]; rfl

theorem primrec_fixed_fin_flatMap {k : ℕ} (f : ℕ → Fin k → List ℕ)
    (hf : ∀ i, Primrec (fun n => f n i)) :
    Primrec (fun n => (List.finRange k).flatMap (f n)) := by
  induction k with
  | zero => simpa using (Primrec.const ([] : List ℕ))
  | succ k ih =>
    have htail := ih (fun n i => f n i.succ) (fun i => hf i.succ)
    simpa [List.finRange_succ, List.flatMap_map, Function.comp_def] using
      Primrec.list_append.comp (hf 0) htail

theorem primrec_term_subst_tokens {α β : Type*} [Encodable β]
    (t : language.Term α) (tf : ℕ → α → language.Term β)
    (hf : ∀ a, Primrec (fun n => (tf n a).listEncode.map encode)) :
    Primrec (fun n => (t.subst (tf n)).listEncode.map encode) := by
  induction t with
  | var a => exact hf a
  | @func k f ts ih =>
    have htail := primrec_fixed_fin_flatMap
      (fun n i => ((ts i).subst (tf n)).listEncode.map encode) ih
    simpa only [Term.subst, Term.listEncode, List.map_cons, List.map_flatMap] using
      Primrec.list_cons.comp
        (Primrec.const (encode (Sum.inr (⟨k, f⟩ : Σ k, language.Functions k) : β ⊕ _))) htail

theorem numeralTerm_relabel {α β : Type*} (f : α → β) (n : ℕ) :
    (numeralTerm n : language.Term α).relabel f = numeralTerm n := by
  induction n with
  | zero =>
    change Term.func _ (fun i => (Fin.elim0 i : language.Term α).relabel f) = Term.func _ Fin.elim0
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    change Term.func _ (fun i => (![numeralTerm n] i).relabel f) = Term.func _ ![numeralTerm n]
    congr 1
    funext i
    fin_cases i
    exact ih

theorem primrec_numeral_tokens {α : Type*} [Encodable α] :
    Primrec (fun n => (numeralTerm n : language.Term α).listEncode.map encode) := by
  let base := (numeralTerm 0 : language.Term α).listEncode.map encode
  let symbol := encode (Sum.inr (⟨1, ⟨0, by decide⟩⟩ : Σ k, language.Functions k) : α ⊕ _)
  have hrec : Primrec (Nat.rec base (fun _ l => symbol :: l)) :=
    Primrec.nat_rec₁ base (Primrec.list_cons.comp (Primrec.const symbol) Primrec.snd)
  apply hrec.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change symbol :: Nat.rec base (fun _ l => symbol :: l) n = _
    rw [ih]
    simp [numeralTerm, Term.listEncode, List.finRange_succ, symbol]

theorem primrec_formula_numeral_subst_tokens {k : ℕ}
    (φ : language.BoundedFormula ℕ k) (env : ℕ → ℕ → ℕ)
    (henv : ∀ i, Primrec (fun n => env n i)) :
    Primrec (fun n => (φ.subst (fun i => numeralTerm (env n i)) :
      language.BoundedFormula Empty k).listEncode.map encode) := by
  induction φ with
  | falsum => exact Primrec.const _
  | @equal k t u =>
    let tf : ℕ → ℕ ⊕ Fin k → language.Term (Empty ⊕ Fin k) :=
      fun n => Sum.elim (fun i => (numeralTerm (env n i) : language.Term Empty).relabel Sum.inl)
        (Term.var ∘ Sum.inr)
    have hf (a : ℕ ⊕ Fin k) : Primrec (fun n => (tf n a).listEncode.map encode) := by
      cases a with
      | inl i => simpa only [tf, Sum.elim_inl, numeralTerm_relabel] using
          primrec_numeral_tokens.comp (henv i)
      | inr i => exact Primrec.const _
    have ht := Primrec.encode.comp (primrec_term_subst_tokens t tf hf)
    have hu := Primrec.encode.comp (primrec_term_subst_tokens u tf hf)
    have ht' : Primrec (fun n => 2 * Nat.pair k (encode (t.subst (tf n)))) := by
      apply (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.const k) ht)).of_eq
      intro n; rw [encode_list_map_encode]; rfl
    have hu' : Primrec (fun n => 2 * Nat.pair k (encode (u.subst (tf n)))) := by
      apply (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.const k) hu)).of_eq
      intro n; rw [encode_list_map_encode]; rfl
    apply (Primrec.list_cons.comp ht' (Primrec.list_cons.comp hu' (Primrec.const []))).of_eq
    intro n
    simp only [BoundedFormula.subst, BoundedFormula.mapTermRel, BoundedFormula.listEncode,
      List.map_cons, List.map_nil, encode_inl, encode_sigma_val]
    rfl
  | rel r ts => cases r
  | imp φ ψ ihφ ihψ =>
    simpa only [BoundedFormula.subst, BoundedFormula.mapTermRel, BoundedFormula.listEncode,
      List.map_append, List.map_cons] using
      Primrec.list_append.comp (Primrec.list_cons.comp (Primrec.const _) ihφ) ihψ
  | all φ ih =>
    simpa only [BoundedFormula.subst, BoundedFormula.mapTermRel, BoundedFormula.listEncode,
      List.map_cons, id_eq] using Primrec.list_cons.comp (Primrec.const _) ih

/-- Ground numeral instances are primitive recursive in the original sentence
code, even though the fixed formula itself may have been chosen classically. -/
theorem primrec_numeral_instance_code (φ : language.Formula ℕ) (env : ℕ → ℕ → ℕ)
    (henv : ∀ i, Primrec (fun n => env n i)) :
    Primrec (fun n => code (numeralInstance φ (env n))) := by
  apply (Primrec.encode.comp (primrec_formula_numeral_subst_tokens φ env henv)).of_eq
  intro n
  exact encode_list_map_encode _

theorem primrec_program_sentence_code : Primrec (fun n => code (programSentence n)) := by
  apply primrec_numeral_instance_code
  intro i
  by_cases hi : i = 0
  · apply Primrec.id.of_eq
    intro n; simp [programEnv, hi]
  · simpa [programEnv, hi] using (Primrec.const (0 : ℕ))

theorem primrec_program_sentence_not_code : Primrec (fun n => code (programSentence n).not) := by
  have h := primrec_numeral_instance_code
    (rosserFormula 1 2 programWitnesses.positive programWitnesses.negative).not programEnv
    (by
      intro i
      by_cases hi : i = 0
      · apply Primrec.id.of_eq
        intro n; simp [programEnv, hi]
      · simpa [programEnv, hi] using (Primrec.const (0 : ℕ)))
  exact h

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_numeral_instance_code
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_program_sentence_code
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_program_sentence_not_code

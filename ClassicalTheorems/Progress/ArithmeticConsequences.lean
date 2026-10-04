/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticEncoding
import ClassicalTheorems.Progress.ArithmeticEffectiveSubstitution
import ClassicalTheorems.Progress.FoundationEffectiveConsequences

/-! Pull enumerable semantic consequences back along effectively coded
sentence families. This uses the original encoding, not a new proof-specific
encoding. The completed Q proof instead transfers enumerable axioms and
primitive-recursive Rosser instances through the exact-symbol proof language. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

def semanticClosure (theory : language.Theory) : language.Theory :=
  {φ | theory ⊨ᵇ φ}

/-- Enumerability of semantic consequences in the Robinson-Q theorem’s exact
sentence encoding. This is a sufficient alternative hypothesis; the final Q proof uses
enumerability of the translated axiom set directly. -/
def EnumerableConsequences (theory : language.Theory) : Prop :=
  RecursivelyEnumerable (semanticClosure theory)

theorem enumerable_consequences_family (theory : language.Theory)
    (h : EnumerableConsequences theory) (sentence : ℕ → language.Sentence)
    (hsentence : Computable (fun n => code (sentence n))) :
    REPred (fun n => theory ⊨ᵇ sentence n) := by
  have hp : REPred (fun n => ∃ φ, theory ⊨ᵇ φ ∧ code φ = n) := h
  apply (REPred.comp hsentence hp).of_eq
  intro n
  constructor
  · rintro ⟨φ, hφ, he⟩
    have he := arithmetic_code_injective he
    simpa only [he] using hφ
  · intro hφ
    exact ⟨sentence n, hφ, rfl⟩

theorem enumerable_program_consequences (theory : language.Theory)
    (h : EnumerableConsequences theory) :
    REPred (fun n => theory ⊨ᵇ programSentence n) :=
  enumerable_consequences_family theory h programSentence primrec_program_sentence_code.to_comp

theorem enumerable_program_neg_consequences (theory : language.Theory)
    (h : EnumerableConsequences theory) :
    REPred (fun n => theory ⊨ᵇ (programSentence n).not) :=
  enumerable_consequences_family theory h (fun n => (programSentence n).not)
    primrec_program_sentence_not_code.to_comp

/-- Reuse Foundation's actual proof enumerator through an effective code
translation. This generic reduction is retained as a supporting result. The
completed exact-symbol bridge uses ArithmeticProofAxioms and proves the
original general Q theorem without assuming this translation. -/
theorem enumerable_family_of_proof_translation (theory : language.Theory)
    (proofTheory : FFL.FirstOrder.ArithmeticTheory) [proofTheory.RE]
    (translate : ℕ → FFL.FirstOrder.ArithmeticSentence) (htranslate : Computable translate)
    (sentence : ℕ → language.Sentence) (hsentence : Computable (fun n => code (sentence n)))
    (hcorrect : ∀ n, proofTheory ⊢ translate (code (sentence n)) ↔ theory ⊨ᵇ sentence n) :
    REPred (fun n => theory ⊨ᵇ sentence n) :=
  (REPred.comp (htranslate.comp hsentence) (foundation_provability_re proofTheory)).of_eq hcorrect

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.enumerable_consequences_family
#check_upstream ClassicalTheorems.Progress.Arithmetic.enumerable_program_consequences
#check_upstream ClassicalTheorems.Progress.Arithmetic.enumerable_program_neg_consequences
#check_upstream ClassicalTheorems.Progress.Arithmetic.enumerable_family_of_proof_translation

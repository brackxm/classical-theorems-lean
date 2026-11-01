/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Godel
import Mathlib.Tactic.NormNum

/-!
# Arithmetic semantics and a concrete application of Gödel–Rosser

Check nested named quantifiers, shadowing and an unrelated free variable in
the standard natural-number model. The true and false quantifier orders must
remain distinct after translation to Foundation and code decoding.

The finite extension of exact Robinson arithmetic by (2 + 3) * 4 = 20 is
enumerable and has the standard model, so the public incompleteness theorem
applies with inhabited hypotheses. Adding the negation of a Robinson axiom
instead gives an unsatisfiable theory, outside the theorem's hypotheses.
-/

noncomputable section
open Classical Set
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
open ClassicalTheorems.Progress.Arithmetic

namespace ClassicalTheoremsTest.Godel

private def numeral : ℕ → T
  | 0 => zero
  | n + 1 => succ (numeral n)

private theorem realize_numeral (env : ℕ → ℕ) (n : ℕ) : (numeral n).realize env = n := by
  induction n with
  | zero => simp [numeral]
  | succ n ih => simp [numeral, ih]

private def every_has_successor : language.Sentence :=
  closeAll (allV 0 (exV 1 ((v 1).equal (succ (v 0)))))

private def one_successor_for_all : language.Sentence :=
  closeAll (exV 1 (allV 0 ((v 1).equal (succ (v 0)))))

/-- ∀x ∃y, y = x + 1 is true, while ∃y ∀x, y = x + 1 is false. -/
theorem quantifier_order : (ℕ ⊨ every_has_successor) ∧ ¬(ℕ ⊨ one_successor_for_all) := by
  constructor
  · rw [every_has_successor, realize_closeAll]
    intro env
    rw [realize_allV]
    intro x
    rw [realize_exV]
    refine ⟨Nat.succ x, ?_⟩
    simp [Formula.realize_equal]
  · rw [one_successor_for_all, realize_closeAll]
    intro h
    obtain ⟨y, hy⟩ := (realize_exV _ _ _).mp (h (fun _ => 0))
    rw [realize_allV] at hy
    have h0 := hy 0
    have h1 := hy 1
    simp [Formula.realize_equal] at h0 h1
    omega

/-- An inner quantifier with the same name shadows its outer binder. -/
theorem shadowing : ℕ ⊨ closeAll (allV 0 (exV 0 ((v 0).equal zero))) := by
  rw [realize_closeAll]
  intro env
  rw [realize_allV]
  intro x
  rw [realize_exV]
  refine ⟨0, ?_⟩
  simp [Formula.realize_equal]

/-- Binding variable 0 preserves the value of the unrelated free variable 7. -/
theorem free_variable_semantics (env : ℕ → ℕ) :
    (allV 0 ((v 7).equal (numeral 5))).Realize env ↔ env 7 = 5 := by
  rw [realize_allV]
  simp [Formula.realize_equal, realize_numeral]

/-- Universal closure binds that remaining free variable instead of choosing a valuation. -/
theorem closure_binds_free_variable :
    ¬(ℕ ⊨ closeAll (allV 0 ((v 7).equal (numeral 5)))) := by
  rw [realize_closeAll]
  intro h
  have hh := (free_variable_semantics (fun _ => 6)).mp (h (fun _ => 6))
  norm_num at hh

local instance : FFL.FirstOrder.Tarski.Structure proofLanguage ℕ := exportProofStructure ℕ

private theorem translation_realizes (φ : language.Sentence) :
    (toProofSentence φ).Realize ℕ ↔ ℕ ⊨ φ :=
  toProofSentence_realize φ (by intros; rfl) (by intro ys; rfl)

/-- The bound-variable reversal in the proof-language bridge preserves both truth values. -/
theorem translated_quantifier_order :
    (toProofSentence every_has_successor).Realize ℕ ∧
    ¬(toProofSentence one_successor_for_all).Realize ℕ := by
  constructor
  · exact (translation_realizes _).mpr quantifier_order.1
  · intro h
    exact quantifier_order.2 ((translation_realizes _).mp h)

private theorem decode_roundtrip (φ : language.Sentence) :
    readOriginalSentenceCode (toProofSentence φ) = some (code φ) := by
  rw [readOriginalSentenceCode_eq, toProofSentence, fromProofFormula_to]
  rfl

/-- Both differently quantified sentences survive the effective coding round trip. -/
theorem encoding_roundtrip :
    readOriginalSentenceCode (toProofSentence every_has_successor) = some (code every_has_successor) ∧
    readOriginalSentenceCode (toProofSentence one_successor_for_all) = some (code one_successor_for_all) ∧
    code every_has_successor ≠ code one_successor_for_all := by
  refine ⟨decode_roundtrip _, decode_roundtrip _, ?_⟩
  intro h
  have he := arithmetic_code_injective h
  exact quantifier_order.2 (he ▸ quantifier_order.1)

private def arithmetic_fact : language.Sentence :=
  closeAll ((mul (add (numeral 2) (numeral 3)) (numeral 4)).equal (numeral 20))

private theorem natural_fact : ℕ ⊨ arithmetic_fact := by
  rw [arithmetic_fact, realize_closeAll]
  intro env
  norm_num [Formula.realize_equal, realize_numeral]

private def extension : language.Theory := robinson ∪ {arithmetic_fact}

private instance natural_extension : ℕ ⊨ extension := by
  rw [Theory.model_iff]
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact Theory.realize_sentence_of_mem robinson hφ
  · rw [Set.mem_singleton_iff.mp hφ]
    exact natural_fact

/-- All three Gödel hypotheses hold for this explicit finite arithmetic extension. -/
theorem extension_hypotheses :
    robinson ⊆ extension ∧ RecursivelyEnumerable extension ∧ extension.IsSatisfiable := by
  refine ⟨Set.subset_union_left, ?_, Theory.Model.isSatisfiable ℕ⟩
  have hf : extension.Finite := robinson_finite.union (Set.finite_singleton arithmetic_fact)
  let codes := (hf.image code).toFinset
  have he : (fun n : ℕ => ∃ φ ∈ extension, code φ = n) = (fun n => n ∈ codes) := by
    funext n
    apply propext
    simp [codes]
  unfold RecursivelyEnumerable
  rw [he]
  exact (primrec_finite_membership codes).computablePred.to_re

/-- Apply the public theorem with proved enumerability and an actual standard model. -/
theorem godel_on_extension :
    ∃ φ : language.Sentence, (extension ∪ {φ}).IsSatisfiable ∧
      (extension ∪ {φ.not}).IsSatisfiable :=
  ClassicalTheorems.godel_incompleteness extension extension_hypotheses.1
    extension_hypotheses.2.1 extension_hypotheses.2.2

private def successor_nonzero : language.Sentence := closeAll ((succ (v 0)).equal zero).not
private def contradictory : language.Theory := robinson ∪ {successor_nonzero.not}

/-- A theory containing a Robinson axiom and its negation fails the satisfiability premise. -/
theorem contradiction_rejected : ¬contradictory.IsSatisfiable := by
  intro hs
  let M := hs.some
  have hp : M ⊨ successor_nonzero := Theory.realize_sentence_of_mem contradictory
    (Or.inl (by simp [robinson, successor_nonzero]))
  have hn : M ⊨ successor_nonzero.not := Theory.realize_sentence_of_mem contradictory
    (Or.inr (Set.mem_singleton _))
  exact (Sentence.realize_not M).mp hn hp

#check_upstream quantifier_order
#check_upstream shadowing
#check_upstream free_variable_semantics
#check_upstream closure_binds_free_variable
#check_upstream translated_quantifier_order
#check_upstream encoding_roundtrip
#check_upstream extension_hypotheses
#check_upstream godel_on_extension
#check_upstream contradiction_rejected

end ClassicalTheoremsTest.Godel

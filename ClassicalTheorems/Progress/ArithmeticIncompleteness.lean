/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticConsequences
import ClassicalTheorems.Progress.ArithmeticProofInstances
import ClassicalTheorems.Progress.ArithmeticProofAxioms

/-! A checked reduction of semantic incompleteness to effective arithmetic
separation. The Robinson-Q sentence family and its primitive-recursive codes
are constructed. Translation to Foundation's calculus preserves arbitrary
models, semantic consequences and provability. Its effective partial inverse
transfers enumerability from the original axiom encoding, completing the
Gödel–Rosser theorem for every satisfiable enumerable extension of exact Q. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language
namespace ClassicalTheorems.Progress.Arithmetic

theorem extension_satisfiable_iff_not_models_neg {L : _root_.FirstOrder.Language}
    (theory : L.Theory) (φ : L.Sentence) :
    (theory ∪ {φ}).IsSatisfiable ↔ ¬ theory ⊨ᵇ φ.not := by
  constructor
  · intro hs hn
    let M := hs.some
    have hφ : M ⊨ φ := Theory.realize_sentence_of_mem (theory ∪ {φ})
      (Set.subset_union_right (Set.mem_singleton φ))
    let : M ⊨ theory := Theory.Model.mono M.is_model Set.subset_union_left
    exact (Sentence.realize_not M).mp (hn.realize_sentence M) hφ
  · intro hn
    rw [Theory.models_sentence_iff] at hn
    push Not at hn
    obtain ⟨M, hM⟩ := hn
    have hφ : M ⊨ φ := by simpa only [Sentence.realize_not, not_not] using hM
    let : M ⊨ theory ∪ {φ} := by
      rw [Theory.model_iff]
      intro ψ hψ
      rcases hψ with hψ | hψ
      · exact Theory.realize_sentence_of_mem theory hψ
      · simpa only [Set.mem_singleton_iff.mp hψ] using hφ
    exact Theory.Model.isSatisfiable M

/-- The optional statement's two satisfiable extensions express exactly
failure of completeness, once the theory is satisfiable. -/
theorem independent_sentence_iff_not_complete {L : _root_.FirstOrder.Language}
    (theory : L.Theory) (hs : theory.IsSatisfiable) :
    (∃ φ : L.Sentence, (theory ∪ {φ}).IsSatisfiable ∧
      (theory ∪ {φ.not}).IsSatisfiable) ↔ ¬ theory.IsComplete := by
  simp only [extension_satisfiable_iff_not_models_neg]
  have hdneg (φ : L.Sentence) : theory ⊨ᵇ φ.not.not ↔ theory ⊨ᵇ φ := by
    simp only [Theory.models_sentence_iff, Sentence.realize_not, not_not]
  simp only [hdneg, Theory.IsComplete, hs, true_and, not_forall, not_or]
  constructor <;> rintro ⟨φ, h1, h2⟩ <;> exact ⟨φ, h2, h1⟩

theorem robinson_not_complete : ¬ ClassicalTheorems.Statements.Arithmetic.robinson.IsComplete :=
  (independent_sentence_iff_not_complete _ robinson_satisfiable).mp
    ⟨zeroMultiplication, robinson_independent_sentence⟩

/-- A consistent theory that effectively separates the two diagonal program
outcomes must be incomplete. The explicit assumptions isolate the arithmetic
representation and proof-enumeration obligations rather than assuming them. -/
theorem independent_sentence_of_diagonal_representation
    {L : _root_.FirstOrder.Language} (theory : L.Theory)
    (hs : theory.IsSatisfiable) (sentence : ℕ → L.Sentence)
    (hzero : ∀ n, diagonalOutput 0 n → theory ⊨ᵇ sentence n)
    (hone : ∀ n, diagonalOutput 1 n → theory ⊨ᵇ (sentence n).not)
    (hEnumerable : REPred (fun n => theory ⊨ᵇ sentence n))
    (hNegEnumerable : REPred (fun n => theory ⊨ᵇ (sentence n).not)) :
    ∃ φ : L.Sentence, (theory ∪ {φ}).IsSatisfiable ∧
      (theory ∪ {φ.not}).IsSatisfiable := by
  apply (independent_sentence_iff_not_complete theory hs).mpr
  intro hc
  have hComplement : REPred (fun n => ¬ theory ⊨ᵇ sentence n) :=
    hNegEnumerable.of_eq (fun n => hc.models_not_iff (sentence n))
  have hComputable : ComputablePred (fun n => theory ⊨ᵇ sentence n) :=
    ComputablePred.computable_iff_re_compl_re'.mpr ⟨hEnumerable, hComplement⟩
  apply diagonal_output_inseparable _ hComputable hzero
  intro n hn
  exact (hc.models_not_iff (sentence n)).mp (hone n hn)

/-- Reduction for any bounded program representation. The representation is
instantiated by `programWitnesses` below. -/
theorem independent_sentence_of_bounded_program_witnesses
    (data : BoundedProgramWitnesses) (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hs : theory.IsSatisfiable)
    (hEnumerable : REPred (fun n => theory ⊨ᵇ boundedProgramSentence data n))
    (hNegEnumerable : REPred (fun n => theory ⊨ᵇ (boundedProgramSentence data n).not)) :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable := by
  have extend {φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence}
      (hφ : ClassicalTheorems.Statements.Arithmetic.robinson ⊨ᵇ φ) : theory ⊨ᵇ φ :=
    Theory.models_of_models_theory
      (fun ψ hψ => Theory.models_sentence_of_mem (hArithmetic hψ)) hφ
  exact independent_sentence_of_diagonal_representation theory hs (boundedProgramSentence data)
    (fun n hn => extend (bounded_program_sentence_zero data n hn))
    (fun n hn => extend (bounded_program_sentence_one data n hn)) hEnumerable hNegEnumerable

/-- The actual program sentence family gives an independent sentence as soon
as its positive and negative consequences are enumerable. The completed
proof-language bridge derives these hypotheses from the original exact
encoded axiom-enumerability predicate. -/
theorem independent_sentence_of_enumerable_program_consequences
    (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hs : theory.IsSatisfiable)
    (hEnumerable : REPred (fun n => theory ⊨ᵇ programSentence n))
    (hNegEnumerable : REPred (fun n => theory ⊨ᵇ (programSentence n).not)) :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable :=
  independent_sentence_of_bounded_program_witnesses programWitnesses theory
    hArithmetic hs hEnumerable hNegEnumerable

/-- Every satisfiable extension of Q whose semantic consequences are
enumerable in the original sentence encoding is incomplete. This is an alternative sufficient condition; the final general theorem
uses effective translation of the axioms and the program instances. -/
theorem independent_sentence_of_enumerable_consequences
    (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hs : theory.IsSatisfiable) (h : EnumerableConsequences theory) :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable :=
  independent_sentence_of_enumerable_program_consequences theory hArithmetic hs
    (enumerable_program_consequences theory h) (enumerable_program_neg_consequences theory h)

/-- The semantic bridge and the effectively translated Rosser family reduce
the general theorem to enumerability of translated axioms. The partial
inverse establishes this from the original encoded predicate. -/
theorem independent_sentence_of_enumerable_proof_axioms
    (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hs : theory.IsSatisfiable) [(toProofTheory theory).RE] :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable := by
  have hp := proofLanguage_provability_re (toProofTheory theory)
  exact independent_sentence_of_enumerable_program_consequences theory hArithmetic hs
    ((REPred.comp primrec_toProof_programSentence.to_comp hp).of_eq
      (fun n => toProofTheory_provable theory (programSentence n)))
    ((REPred.comp primrec_toProof_programSentence_not.to_comp hp).of_eq
      (fun n => toProofTheory_provable theory (programSentence n).not))

/-- Every satisfiable finite extension of the exact seven Q axioms is
incomplete. Finiteness already supplies enumerability of translated axioms,
so this result needs no remaining code-translation hypothesis. -/
theorem independent_sentence_of_finite_extension
    (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hs : theory.IsSatisfiable) (hfinite : Set.Finite theory) :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable := by
  have hproof : Set.Finite (toProofTheory theory) :=
    (hfinite.image toProofSentence).union proof_equality_axioms_finite
  let : (toProofTheory theory).RE := FFL.FirstOrder.Theory.RE.ofFinite hproof
  exact independent_sentence_of_enumerable_proof_axioms theory hArithmetic hs

/-- Gödel–Rosser incompleteness with the original language, seven Robinson
axioms and exact recursively enumerable sentence-code predicate. -/
theorem independent_sentence_of_recursively_enumerable_extension
    (theory : ClassicalTheorems.Statements.Arithmetic.language.Theory)
    (hArithmetic : ClassicalTheorems.Statements.Arithmetic.robinson ⊆ theory)
    (hEnumerable : ClassicalTheorems.Statements.Arithmetic.RecursivelyEnumerable theory)
    (hs : theory.IsSatisfiable) :
    ∃ φ : ClassicalTheorems.Statements.Arithmetic.language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable := by
  let : (toProofTheory theory).RE := toProofTheory_recursivelyEnumerable theory hEnumerable
  exact independent_sentence_of_enumerable_proof_axioms theory hArithmetic hs

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_not_complete
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_iff_not_complete
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_diagonal_representation
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_bounded_program_witnesses
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_enumerable_program_consequences
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_enumerable_consequences
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_enumerable_proof_axioms
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_finite_extension
#check_upstream ClassicalTheorems.Progress.Arithmetic.independent_sentence_of_recursively_enumerable_extension

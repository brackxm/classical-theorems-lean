/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.FoundationArithmeticTranslation
import ClassicalTheorems.Progress.RobinsonSeparation

/-! Actual bounded program witnesses in the exact language of Robinson Q.
Foundation supplies standard arithmetic representation and prenex matrices;
the checked local translation supplies the bounded formulas and freshness
certificates required by the existing Rosser construction. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

/-- Every r.e. predicate is represented by a bounded matrix with input
variable 0 and witness variable 1. No other variable occurs freely. -/
theorem re_predicate_robinson_witness (p : ℕ → Prop) (hp : REPred p) :
    ∃ ψ : language.Formula ℕ, DeltaZero ψ ∧ ψ.freeVarFinset ⊆ {0, 1} ∧
      ∀ n, p n ↔ ∃ w, ψ.Realize (Function.update (programEnv n) 1 w) := by
  obtain ⟨matrix, hmatrix⟩ := re_predicate_bounded_matrix p hp
  obtain ⟨ψ, hψ, hs, hspec⟩ := foundation_bounded_translation matrix.val matrix.bounded ![1, 0]
  refine ⟨ψ, hψ, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (hs ha)
    fin_cases i <;> simp
  · intro n
    rw [hmatrix n]
    apply exists_congr
    intro w
    rw [hspec]
    have he : Function.update (programEnv n) 1 w ∘ (![1, 0] : Fin 2 → ℕ) = ![w, n] := by
      funext i
      fin_cases i <;> simp [programEnv]
    rw [he]

/-- The computation encoding required by the Rosser reduction exists.
This is a proved existence result, rather than an assumed representation. -/
theorem bounded_program_witnesses_exist : Nonempty BoundedProgramWitnesses := by
  obtain ⟨positive, hp, hps, hspecp⟩ :=
    re_predicate_robinson_witness (diagonalOutput 0) (diagonal_output_re 0)
  obtain ⟨negative, hq, hqs, hspecq⟩ :=
    re_predicate_robinson_witness (diagonalOutput 1) (diagonal_output_re 1)
  refine ⟨{
    positive := positive
    negative := negative
    positive_bounded := hp
    negative_bounded := hq
    negative_fresh := ?_
    positive_spec := hspecp
    negative_spec := hspecq }⟩
  intro h
  have := hqs h
  simp at this

def programWitnesses : BoundedProgramWitnesses := Classical.choice bounded_program_witnesses_exist

def programSentence (n : ℕ) : language.Sentence := boundedProgramSentence programWitnesses n

theorem program_sentence_zero (n : ℕ) (h : diagonalOutput 0 n) :
    robinson ⊨ᵇ programSentence n := bounded_program_sentence_zero programWitnesses n h

theorem program_sentence_one (n : ℕ) (h : diagonalOutput 1 n) :
    robinson ⊨ᵇ (programSentence n).not := bounded_program_sentence_one programWitnesses n h

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.re_predicate_robinson_witness
#check_upstream ClassicalTheorems.Progress.Arithmetic.bounded_program_witnesses_exist
#check_upstream ClassicalTheorems.Progress.Arithmetic.program_sentence_zero
#check_upstream ClassicalTheorems.Progress.Arithmetic.program_sentence_one

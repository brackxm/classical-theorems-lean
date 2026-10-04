/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonRepresentation
import ClassicalTheorems.Progress.InseparablePrograms

/-! Rosser separation from bounded arithmetic program witnesses. The sentence
is constructed in the original language. `RobinsonProgramWitnesses` constructs
an inhabitant of the witness structure defined here. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

theorem robinson_rosser_positive (i j : ℕ) (positive negative : language.Formula ℕ)
    (hp : DeltaZero positive) (hq : DeltaZero negative) (hij : i ≠ j)
    (hfresh : j ∉ negative.freeVarFinset) (env : ℕ → ℕ)
    (hpos : ∃ n, positive.Realize (Function.update env i n))
    (hneg : ∀ n, ¬ negative.Realize (Function.update env i n)) :
    robinson ⊨ᵇ numeralInstance (rosserFormula i j positive negative) env := by
  rw [Theory.models_sentence_iff]
  intro M
  rw [realize_numeralInstance, realize_rosserFormula i j positive negative hij hfresh]
  have hp' (n : ℕ) :
      positive.Realize (Function.update (fun k => modelNumeral (M := M) (env k)) i (modelNumeral n)) ↔
        positive.Realize (Function.update env i n) := by
    rw [numeral_update]
    exact deltaZero_absolute hp _
  have hq' (n : ℕ) :
      negative.Realize (Function.update (fun k => modelNumeral (M := M) (env k)) i (modelNumeral n)) ↔
        negative.Realize (Function.update env i n) := by
    rw [numeral_update]
    exact deltaZero_absolute hq _
  exact rosser_comparison_positive _ _ _ _ hp' hq' hpos hneg

theorem robinson_rosser_negative (i j : ℕ) (positive negative : language.Formula ℕ)
    (hp : DeltaZero positive) (hq : DeltaZero negative) (hij : i ≠ j)
    (hfresh : j ∉ negative.freeVarFinset) (env : ℕ → ℕ)
    (hpos : ∀ n, ¬ positive.Realize (Function.update env i n))
    (hneg : ∃ n, negative.Realize (Function.update env i n)) :
    robinson ⊨ᵇ (numeralInstance (rosserFormula i j positive negative) env).not := by
  rw [Theory.models_sentence_iff]
  intro M
  rw [Sentence.realize_not, realize_numeralInstance,
    realize_rosserFormula i j positive negative hij hfresh]
  have hp' (n : ℕ) :
      positive.Realize (Function.update (fun k => modelNumeral (M := M) (env k)) i (modelNumeral n)) ↔
        positive.Realize (Function.update env i n) := by
    rw [numeral_update]
    exact deltaZero_absolute hp _
  have hq' (n : ℕ) :
      negative.Realize (Function.update (fun k => modelNumeral (M := M) (env k)) i (modelNumeral n)) ↔
        negative.Realize (Function.update env i n) := by
    rw [numeral_update]
    exact deltaZero_absolute hq _
  exact rosser_comparison_negative _ _ _ _ hp' hq' hpos hneg

def programEnv (n : ℕ) : ℕ → ℕ := fun i => if i = 0 then n else 0

/-- Bounded witness matrices for the two actual partial-recursive program
outcomes. The `RobinsonProgramWitnesses` module proves existence. -/
structure BoundedProgramWitnesses where
  positive : language.Formula ℕ
  negative : language.Formula ℕ
  positive_bounded : DeltaZero positive
  negative_bounded : DeltaZero negative
  negative_fresh : 2 ∉ negative.freeVarFinset
  positive_spec : ∀ n, diagonalOutput 0 n ↔
    ∃ w, positive.Realize (Function.update (programEnv n) 1 w)
  negative_spec : ∀ n, diagonalOutput 1 n ↔
    ∃ w, negative.Realize (Function.update (programEnv n) 1 w)

def boundedProgramSentence (data : BoundedProgramWitnesses) (n : ℕ) : language.Sentence :=
  numeralInstance (rosserFormula 1 2 data.positive data.negative) (programEnv n)

theorem bounded_program_sentence_zero (data : BoundedProgramWitnesses) (n : ℕ)
    (hn : diagonalOutput 0 n) : robinson ⊨ᵇ boundedProgramSentence data n := by
  apply robinson_rosser_positive 1 2 data.positive data.negative
    data.positive_bounded data.negative_bounded (by decide) data.negative_fresh
    (programEnv n) ((data.positive_spec n).mp hn)
  intro w hw
  exact diagonal_output_disjoint n ⟨hn, (data.negative_spec n).mpr ⟨w, hw⟩⟩

theorem bounded_program_sentence_one (data : BoundedProgramWitnesses) (n : ℕ)
    (hn : diagonalOutput 1 n) : robinson ⊨ᵇ (boundedProgramSentence data n).not := by
  apply robinson_rosser_negative 1 2 data.positive data.negative
    data.positive_bounded data.negative_bounded (by decide) data.negative_fresh
    (programEnv n) ?_ ((data.negative_spec n).mp hn)
  intro w hw
  exact diagonal_output_disjoint n ⟨(data.positive_spec n).mpr ⟨w, hw⟩, hn⟩

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_rosser_positive
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_rosser_negative
#check_upstream ClassicalTheorems.Progress.Arithmetic.bounded_program_sentence_zero
#check_upstream ClassicalTheorems.Progress.Arithmetic.bounded_program_sentence_one

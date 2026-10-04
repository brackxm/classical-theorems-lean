/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofFormulaCoding

/-! Enumerability of the translated original axiom set. A primitive-recursive
partial inverse recovers the original sentence code; injectivity of that code
and exact syntax recovery identify membership without changing the axiom set. -/

noncomputable section
open Classical Encodable FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

theorem toProof_image_iff (theory : language.Theory) (σ : FFL.FirstOrder.Sentence proofLanguage) :
    σ ∈ toProofSentence '' theory ↔ ∃ φ, (fromProofFormula σ).1 = some φ ∧ φ ∈ theory := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨φ, congrArg Prod.fst (fromProofFormula_to φ), hφ⟩
  · rintro ⟨φ, hparse, hφ⟩
    exact ⟨φ, hφ, (fromProofFormula_correct σ).1 φ hparse⟩

theorem toProof_image_re (theory : language.Theory) (h : RecursivelyEnumerable theory) :
    REPred (fun σ : FFL.FirstOrder.Sentence proofLanguage => σ ∈ toProofSentence '' theory) := by
  have hread := primrec_readOriginalSentenceCode
  have hparse : ComputablePred (fun σ : FFL.FirstOrder.Sentence proofLanguage =>
      readOriginalSentenceCode σ ≠ none) :=
    (PrimrecPred.not (Primrec.eq.comp hread (Primrec.const none))).computablePred
  have hcode : Computable (fun σ : FFL.FirstOrder.Sentence proofLanguage =>
      (readOriginalSentenceCode σ).getD 0) :=
    (Primrec.option_getD.comp hread (Primrec.const 0)).to_comp
  apply (hparse.to_re.and (REPred.comp hcode h)).of_eq
  intro σ
  rw [toProof_image_iff, readOriginalSentenceCode_eq]
  cases hp : (fromProofFormula σ).1 with
  | none => simp
  | some φ =>
    simp only [Option.map_some, Option.getD_some, ne_eq, Option.some_ne_none, not_false_eq_true,
      true_and, Option.some.injEq]
    constructor
    · rintro ⟨ψ, hψ, he⟩
      have he := arithmetic_code_injective he
      subst ψ
      exact ⟨φ, rfl, hψ⟩
    · rintro ⟨ψ, rfl, hψ⟩
      exact ⟨φ, hψ, rfl⟩

theorem toProofTheory_recursivelyEnumerable (theory : language.Theory)
    (h : RecursivelyEnumerable theory) : (toProofTheory theory).RE :=
  FFL.FirstOrder.Theory.RE.add ⟨toProof_image_re theory h⟩
    (FFL.FirstOrder.Theory.RE.ofFinite proof_equality_axioms_finite)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProof_image_re
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofTheory_recursivelyEnumerable

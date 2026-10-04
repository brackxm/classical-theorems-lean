/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.InseparablePrograms
import Foundation.FirstOrder.Arithmetic.R0.Representation
import Foundation.FirstOrder.Arithmetic.Prenex

/-! Reuse Foundation's arithmetic representation of recursively enumerable
predicates. Prenex normalization is used only over the standard natural
numbers, where its collection hypotheses hold. No collection or induction
axiom is added to Robinson Q. `FoundationArithmeticTranslation` translates
these matrices into the project's first-order syntax. -/

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
namespace ClassicalTheorems.Progress.Arithmetic

/-- Every r.e. predicate has a bounded arithmetic matrix with one numerical
witness. The matrix is obtained from the existing dependency's representation,
rather than copying its computation-coding proof. -/
theorem re_predicate_bounded_matrix (p : ℕ → Prop) (hp : REPred p) :
    ∃ matrix : ℬ[<, ℒₒᵣ].Semisentence 2,
      ∀ n, p n ↔ ∃ w, matrix.val.Evalb ![w, n] := by
  have hSigma : ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 (codeOfREPred p) := by
    simp [codeOfREPred, codeOfPartrec']
  obtain ⟨prenex, hprenex⟩ :=
    Bounding.Prenex.models_exists_prenex (Γ' := 𝚺) hSigma
  refine ⟨prenex.sigmaInv.matrix, ?_⟩
  intro n
  have h := hprenex ℕ ![n] Empty.elim
  rw [Bounding.Prenex.models_sigmaInv] at h
  have hm : prenex.sigmaInv.val = prenex.sigmaInv.matrix.val := rfl
  rw [hm] at h
  exact (codeOfREPred_spec hp).symm.trans h

/-- The two diagonal program outcomes have bounded witness matrices in the
dependency's syntax, ready for the checked local syntax translation. -/
theorem diagonal_output_bounded_matrix (output : ℕ) :
    ∃ matrix : ℬ[<, ℒₒᵣ].Semisentence 2,
      ∀ n, diagonalOutput output n ↔ ∃ w, matrix.val.Evalb ![w, n] :=
  re_predicate_bounded_matrix _ (diagonal_output_re output)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.re_predicate_bounded_matrix
#check_upstream ClassicalTheorems.Progress.Arithmetic.diagonal_output_bounded_matrix

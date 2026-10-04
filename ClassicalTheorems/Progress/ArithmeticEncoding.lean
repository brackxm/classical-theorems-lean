/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import ClassicalTheorems.Statements.Arithmetic

/-! Effective encoding facts for Robinson-Q incompleteness
statement. Its finite axiom set is recursively enumerable in the exact fixed
encoding used by that statement. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

theorem arithmetic_code_injective : Function.Injective code := by
  intro φ ψ h
  have he := Encodable.encode_injective h
  have hs : (⟨0, φ⟩ : Σ n, language.BoundedFormula Empty n) = ⟨0, ψ⟩ :=
    BoundedFormula.listEncode_sigma_injective he
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

theorem robinson_finite : robinson.Finite := by
  simp [robinson]

/-- Membership in an arbitrary fixed finite set of numbers is primitive recursive. -/
theorem primrec_finite_membership (s : Finset ℕ) : PrimrecPred (fun n => n ∈ s) := by
  induction s using Finset.induction_on with
  | empty =>
    apply Primrec.primrecPred
    exact (Primrec.const false).of_eq (fun _ => by simp)
  | @insert n s hn ih =>
    have he : PrimrecPred (fun x : ℕ => x = n) :=
      Primrec.eq.comp Primrec.id (Primrec.const n)
    exact (he.or ih).of_eq (fun _ => by simp)

theorem robinson_recursivelyEnumerable : RecursivelyEnumerable robinson := by
  let codes := (robinson_finite.image code).toFinset
  have he : (fun n : ℕ => ∃ φ ∈ robinson, code φ = n) = (fun n => n ∈ codes) := by
    funext n
    apply propext
    simp [codes]
  unfold RecursivelyEnumerable
  rw [he]
  exact (primrec_finite_membership codes).computablePred.to_re

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.arithmetic_code_injective
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_recursivelyEnumerable

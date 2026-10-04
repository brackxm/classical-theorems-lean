/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Foundation.FirstOrder.Incompleteness.First

/-! Effective consequence enumeration in the existing Foundation dependency.
Craig's trick replaces an enumerable axiom set with an equivalent primitive
recursive theory. Its arithmetized proof predicate and completeness theorem
give enumerable semantic consequences. These metatheorems add no arithmetic
axioms to the theory being studied. The local exact-symbol translation and effective partial inverse transfer
this enumerator to the project's original mathlib axiom predicate. -/

noncomputable section
open Classical FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
namespace ClassicalTheorems.Progress.Arithmetic

theorem foundation_provability_re {L : FFL.FirstOrder.Language}
    [L.Encodable] [L.Primcodable] [L.LORDefinable] [L.DecidableEq]
    (theory : FFL.FirstOrder.Theory L) [theory.RE] :
    REPred (fun σ : FFL.FirstOrder.Sentence L => theory ⊢ σ) := by
  have hdef : 𝚺ᴬ₁-Predicate (Bootstrapping.Provable theory.craig : ℕ → Prop) :=
    Bootstrapping.Provable.definable
  have hRE := rePred_iff_sigma1.mpr hdef
  apply (REPred.comp (Primrec.encode.to_comp : Computable
    (Encodable.encode : FFL.FirstOrder.Sentence L → ℕ)) hRE).of_eq
  intro σ
  have hquote : (⌜σ⌝ : ℕ) = Encodable.encode σ := by
    simp [Sentence.quote_def, Semiformula.quote_eq_encode]
  rw [← hquote, Bootstrapping.provable_iff_provable]
  exact (Entailment.Equiv.iff.mp (inferInstance : theory ≊ theory.craig) σ).symm

/-- Soundness and completeness identify the enumerable proof set with the
semantic consequences in Foundation's own syntax. -/
theorem foundation_semantic_consequences_re {L : FFL.FirstOrder.Language.{0}}
    [L.Encodable] [L.Primcodable] [L.LORDefinable] [L.DecidableEq]
    (theory : FFL.FirstOrder.Theory L) [theory.RE] :
    REPred (fun σ : FFL.FirstOrder.Sentence L => theory ⊨[Tarski.SmallStruc L] σ) :=
  (foundation_provability_re theory).of_eq
    (fun _ => ⟨FFL.FirstOrder.Theory.Proof.sound, FFL.FirstOrder.Theory.Proof.complete.{0, 0}⟩)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.foundation_provability_re
#check_upstream ClassicalTheorems.Progress.Arithmetic.foundation_semantic_consequences_re

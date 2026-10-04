/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.ModelTheory.Satisfiability

/-! Helpers for writing first-order statements with named natural-number variables.
Quantifiers bind free occurrences using mathlib's capture-avoiding relabelling.
These are definitions only; no unproved logical facts are assumed here. -/

namespace ClassicalTheorems.Statements.FirstOrder

open _root_.FirstOrder.Language

abbrev F (L : _root_.FirstOrder.Language) := L.Formula ℕ

def allV {L : _root_.FirstOrder.Language} (i : ℕ) (φ : F L) : F L :=
  (_root_.FirstOrder.Language.BoundedFormula.relabel
    (fun j => if j = i then Sum.inr (0 : Fin 1) else Sum.inl j) φ).all

def exV {L : _root_.FirstOrder.Language} (i : ℕ) (φ : F L) : F L :=
  (allV i φ.not).not

def eqV {L : _root_.FirstOrder.Language} (i j : ℕ) : F L :=
  (Term.var i).equal (Term.var j)

def iffF {L : _root_.FirstOrder.Language} (φ ψ : F L) : F L := φ.iff ψ

def allVars {L : _root_.FirstOrder.Language} (is : List ℕ) (φ : F L) : F L :=
  is.foldr allV φ

/-- Universal closure over precisely the free variables of a formula. -/
noncomputable def closeAll {L : _root_.FirstOrder.Language} (φ : F L) : L.Sentence :=
  φ.not.exClosure.not

end ClassicalTheorems.Statements.FirstOrder

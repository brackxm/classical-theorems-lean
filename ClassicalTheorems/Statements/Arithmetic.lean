/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Statements.FirstOrder
import Mathlib.ModelTheory.Encoding
import Mathlib.Computability.RE

/-! Syntax and effective encoding of the seven Robinson arithmetic axioms. -/

namespace ClassicalTheorems.Statements.Arithmetic

open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder

/-- The language `0, successor, addition, multiplication`. -/
def language : _root_.FirstOrder.Language where
  Functions n := Fin (if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 2 else 0)
  Relations _ := Empty

instance : Encodable (Σ n, language.Functions n) :=
  inferInstanceAs (Encodable (Σ n : ℕ,
    Fin (if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 2 else 0)))

instance : Encodable (Σ n, language.Relations n) :=
  inferInstanceAs (Encodable (Σ _ : ℕ, Empty))

abbrev T := language.Term ℕ

def zero : T := .func ⟨0, by decide⟩ Fin.elim0
def succ (t : T) : T := .func ⟨0, by decide⟩ ![t]
def add (t u : T) : T := .func ⟨0, by decide⟩ ![t, u]
def mul (t u : T) : T := .func ⟨1, by decide⟩ ![t, u]
def v (i : ℕ) : T := .var i

/-- The seven axioms of Robinson's arithmetic Q, universally closed. -/
noncomputable def robinson : language.Theory :=
  {closeAll ((succ (v 0)).equal zero).not,
   closeAll (((succ (v 0)).equal (succ (v 1))).imp ((v 0).equal (v 1))),
   closeAll (((v 0).equal zero).not.imp (exV 1 ((v 0).equal (succ (v 1))))),
   closeAll ((add (v 0) zero).equal (v 0)),
   closeAll ((add (v 0) (succ (v 1))).equal (succ (add (v 0) (v 1)))),
   closeAll ((mul (v 0) zero).equal zero),
   closeAll ((mul (v 0) (succ (v 1))).equal (add (mul (v 0) (v 1)) (v 0)))}

def code (φ : language.Sentence) : ℕ :=
  Encodable.encode φ.listEncode

/-- Recursive enumerability in mathlib's fixed syntactic encoding of sentences. -/
def RecursivelyEnumerable (theory : language.Theory) : Prop :=
  REPred (fun n : ℕ => ∃ φ ∈ theory, code φ = n)

end ClassicalTheorems.Statements.Arithmetic

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticIncompleteness

/-! Gödel–Rosser incompleteness for every satisfiable recursively
 enumerable extension of the exact seven Robinson axioms. The language and
 sentence encoding are the library's definitions. -/

namespace ClassicalTheorems
open Statements.Arithmetic

theorem godel_incompleteness (theory : language.Theory)
    (hArithmetic : robinson ⊆ theory) (hEnumerable : RecursivelyEnumerable theory)
    (hConsistent : theory.IsSatisfiable) :
    ∃ φ : language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable :=
  Progress.Arithmetic.independent_sentence_of_recursively_enumerable_extension
    theory hArithmetic hEnumerable hConsistent

end ClassicalTheorems
#check_upstream ClassicalTheorems.godel_incompleteness

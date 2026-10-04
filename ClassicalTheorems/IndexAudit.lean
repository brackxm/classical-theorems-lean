/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import ClassicalTheorems.Godel
import ClassicalTheorems.Parallel
import ClassicalTheorems.Euler
import ClassicalTheorems.Green
import ClassicalTheorems.Isoperimetric
import ClassicalTheorems.Heron
import ClassicalTheorems.Translations

/-! Eight theorem entries and ten indexed propositions; every transitive axiom must be standard. -/

-- Gödel’s Incompleteness Theorem
#check_indexed ClassicalTheorems.godel_incompleteness

-- The Independence of the Parallel Postulate
#check_indexed ClassicalTheorems.parallel_postulate_independence

-- Polyhedron Formula
#check_indexed ClassicalTheorems.euler_polyhedron

-- Green’s Theorem
#check_indexed ClassicalTheorems.greens_theorem

-- The Isoperimetric Theorem
#check_indexed ClassicalTheorems.isoperimetric_theorem_jordan

-- Heron’s Formula
#check_indexed ClassicalTheorems.heron_area

-- Pascal’s Hexagon Theorem (HOL Light translation)
#check_indexed HOLLightPort.Pascal.pascal
#check_indexed HOLLightPort.Pascal.pascals_hexagon

-- Desargues’s Theorem (HOL Light translation)
#check_indexed HOLLightPort.Desargues.desargues
#check_indexed HOLLightPort.Desargues.desargues_converse

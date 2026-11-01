/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Desargues
import Mathlib.Tactic.NormNum

/-!
# Perspective triangles with a finite Desargues axis

The triangles (3, -1), (2, 0), (3, 0) and (4, -1), (2, 2), (6, 3)
are noncollinear and in perspective from (2, -1). Their corresponding side
intersections are (6, -4), (-6, 0), and (3, -3), on x + 3y + 6 = 0.
The checks exclude zero joins and zero intersections, and exercise both
directions of the public theorem.
-/

namespace ClassicalTheoremsTest.Desargues

open HOLLightPort.Desargues

private abbrev a : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![3, -1, 1], ![2, 0, 1], ![3, 0, 1]]

private abbrev b : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![4, -1, 1], ![2, 2, 1], ![6, 3, 1]]

private abbrev center : Fin 3 → ℚ := ![2, -1, 1]
private abbrev axis : Fin 3 → ℚ := ![1, 3, 6]

/-- Both triangles are genuinely noncollinear. -/
theorem triangle_determinants : a.det = -1 ∧ b.det = -14 := by
  constructor
  · rw [Matrix.det_fin_three]
    norm_num [a]
  · rw [Matrix.det_fin_three]
    norm_num [b]

/-- Every vertex represents a finite projective point. -/
theorem finite_vertices : ∀ i, a i 2 = 1 ∧ b i 2 = 1 := by
  intro i
  fin_cases i <;> norm_num [a, b]

/-- Corresponding vertices are distinct, so their joins are actual projective lines. -/
theorem nonzero_joins : ∀ i, cross (a i) (b i) ≠ 0 := by
  intro i
  fin_cases i <;> norm_num [a, b, cross, funext_iff, Fin.forall_fin_succ]

private theorem perspective :
    center ≠ 0 ∧ ∀ i, dotProduct (cross (a i) (b i)) center = 0 := by
  constructor
  · norm_num [center, funext_iff, Fin.forall_fin_succ]
  · intro i
    fin_cases i <;> norm_num [a, b, center, cross, dotProduct, Fin.sum_univ_succ]

/-- Apply Desargues to the explicit nonzero perspective center. -/
theorem forward_collinearity :
    ∃ line ≠ (0 : Fin 3 → ℚ), ∀ i, dotProduct (meets a b i) line = 0 :=
  desargues a b center perspective.1 perspective.2

/-- Every side intersection is finite, nonzero, and at its expected affine location. -/
theorem expected_intersections :
    ∀ i, let q := meets a b i
      q 2 ≠ 0 ∧
      q 0 / q 2 = (![6, -6, 3] : Fin 3 → ℚ) i ∧
      q 1 / q 2 = (![-4, 0, -3] : Fin 3 → ℚ) i := by
  intro i
  fin_cases i <;> norm_num [a, b, meets, cross]

/-- The three side intersections lie on the explicit nonzero line x + 3y + 6 = 0. -/
theorem expected_axis : axis ≠ 0 ∧ ∀ i, dotProduct (meets a b i) axis = 0 := by
  constructor
  · norm_num [axis, funext_iff, Fin.forall_fin_succ]
  · intro i
    fin_cases i <;> norm_num [a, b, meets, cross, axis, dotProduct, Fin.sum_univ_succ]

/-- The converse applies to the same noncollinear triangles and explicit axis. -/
theorem converse_concurrency :
    ∃ o ≠ (0 : Fin 3 → ℚ), ∀ i, dotProduct (cross (a i) (b i)) o = 0 := by
  apply desargues_converse a b _ _ axis expected_axis.1 expected_axis.2
  · rw [triangle_determinants.1]
    norm_num
  · rw [triangle_determinants.2]
    norm_num

#check_upstream triangle_determinants
#check_upstream finite_vertices
#check_upstream nonzero_joins
#check_upstream forward_collinearity
#check_upstream expected_intersections
#check_upstream expected_axis
#check_upstream converse_concurrency

end ClassicalTheoremsTest.Desargues

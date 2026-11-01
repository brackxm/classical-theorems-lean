/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Pascal
import Mathlib.Tactic.NormNum

/-!
# A nondegenerate Pascal hexagon on a rational parabola

The six affine points (t, t²), for t = 0, 1, 2, 3, 4, 6, lie on x² = yz.
Their opposite-side intersections are (2, 2), (22/7, 52/7), and (-6, -36).
All are finite and lie on 19x - 4y - 30 = 0. The coordinate checks normalize
homogeneous representatives, so their arbitrary nonzero scale is immaterial.
-/

namespace ClassicalTheoremsTest.Pascal

open HOLLightPort.Pascal

private abbrev points : Fin 6 → Fin 3 → ℚ :=
  ![![0, 0, 1], ![1, 1, 1], ![2, 4, 1], ![3, 9, 1], ![4, 16, 1], ![6, 36, 1]]

private abbrev coefficients : Fin 6 → ℚ := ![1, 0, 0, 0, 0, -1]

-- Twice the quadratic form x² - yz, represented by a symmetric matrix.
private abbrev conic : Matrix (Fin 3) (Fin 3) ℚ :=
  ![![2, 0, 0], ![0, 0, -1], ![0, -1, 0]]

private abbrev axis : Fin 3 → ℚ := ![19, -4, -30]

/-- Every point is finite, hence represented by a nonzero homogeneous vector. -/
theorem finite_points : ∀ i, points i 2 = 1 := by
  intro i
  fin_cases i <;> norm_num [points]

/-- No pair represents the same projective point. -/
theorem distinct_points : ∀ i j, i ≠ j → cross (points i) (points j) ≠ 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [points, cross, funext_iff, Fin.forall_fin_succ] at *

private theorem nonzero_coefficients : coefficients ≠ 0 := by
  norm_num [coefficients, funext_iff, Fin.forall_fin_succ]

private theorem points_on_conic :
    ∀ i, dotProduct (veronese (points i)) coefficients = 0 := by
  intro i
  fin_cases i <;>
    norm_num [points, coefficients, veronese, dotProduct, Fin.sum_univ_succ]

/-- Apply the public coefficient formulation to six distinct points on the parabola. -/
theorem coefficient_pascal : (intersections points).det = 0 :=
  pascal points coefficients nonzero_coefficients points_on_conic

/-- The same configuration satisfies the stronger nonsingular-matrix formulation. -/
theorem nonsingular_pascal : (intersections points).det = 0 := by
  apply pascals_hexagon conic points
  · ext i j
    change conic j i = conic i j
    fin_cases i <;> fin_cases j <;> norm_num [conic]
  · rw [Matrix.det_fin_three]
    norm_num [conic]
  · intro i
    fin_cases i <;>
      norm_num [points, conic, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/-- All three intersections are finite and have independently specified affine coordinates. -/
theorem expected_intersections :
    ∀ i, let q := intersections points i
      q 2 ≠ 0 ∧
      q 0 / q 2 = (![2, 22/7, -6] : Fin 3 → ℚ) i ∧
      q 1 / q 2 = (![2, 52/7, -36] : Fin 3 → ℚ) i := by
  intro i
  fin_cases i <;> norm_num [points, intersections, cross]

/-- The Pascal line has the expected nonzero equation 19x - 4y - 30 = 0. -/
theorem expected_axis : axis ≠ 0 ∧ ∀ i, dotProduct (intersections points i) axis = 0 := by
  constructor
  · norm_num [axis, funext_iff, Fin.forall_fin_succ]
  · intro i
    fin_cases i <;>
      norm_num [points, intersections, cross, axis, dotProduct, Fin.sum_univ_succ]

#check_upstream finite_points
#check_upstream distinct_points
#check_upstream coefficient_pascal
#check_upstream nonsingular_pascal
#check_upstream expected_intersections
#check_upstream expected_axis

end ClassicalTheoremsTest.Pascal

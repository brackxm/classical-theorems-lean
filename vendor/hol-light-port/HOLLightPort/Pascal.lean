/- Modified for the ClassicalTheorems project on 2026-10-03: manually re-formalized HOL Light’s homogeneous-coordinate argument in Lean; see upstream.json for its pinned source. -/
/-
Copyright (c) University of Cambridge 1998.
Copyright (c) John Harrison and others 1998-2012.
Lean adaptation: ClassicalTheorems contributors, 2026.
Distributed under the BSD-2-Clause terms in LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace HOLLightPort.Pascal
variable {K : Type*} [Field K]
def cross (v w : Fin 3 → K) : Fin 3 → K :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]
def veronese (v : Fin 3 → K) : Fin 6 → K :=
  ![v 0 ^ 2, v 1 ^ 2, v 2 ^ 2, v 0 * v 1, v 0 * v 2, v 1 * v 2]
def intersections (p : Fin 6 → Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  ![cross (cross (p 0) (p 1)) (cross (p 3) (p 4)),
    cross (cross (p 1) (p 2)) (cross (p 4) (p 5)),
    cross (cross (p 2) (p 3)) (cross (p 5) (p 0))]

-- The determinant identity is the algebraic certificate for Pascal.
theorem certificate (p : Fin 6 → Fin 3 → K) :
    (intersections p).det = Matrix.det (fun i => veronese (p i)) := by
  rw [Matrix.det_fin_three]
  simp only [intersections, cross, veronese, Matrix.det_succ_row_zero (n := 5),
    Matrix.det_succ_row_zero (n := 4), Matrix.det_succ_row_zero (n := 3),
    Matrix.det_fin_three, Matrix.submatrix_apply, Fin.sum_univ_succ]
  norm_num [Fin.succAbove]
  ring!

/-- Pascal for six homogeneous points on a nonzero quadratic conic. -/
theorem pascal (p : Fin 6 → Fin 3 → K) (coeff : Fin 6 → K)
    (hc : coeff ≠ 0) (hp : ∀ i, dotProduct (veronese (p i)) coeff = 0) :
    (intersections p).det = 0 := by
  rw [certificate]
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨coeff, hc, funext hp⟩

/-- The original indexed statement: a symmetric nonsingular conic matrix. -/
theorem pascals_hexagon [CharZero K] (A : Matrix (Fin 3) (Fin 3) K)
    (p : Fin 6 → Fin 3 → K) (hs : A.transpose = A) (ha : A.det ≠ 0)
    (hp : ∀ i, dotProduct (p i) (A.mulVec (p i)) = 0) :
    (intersections p).det = 0 := by
  let c : Fin 6 → K := ![A 0 0, A 1 1, A 2 2, 2 * A 0 1, 2 * A 0 2, 2 * A 1 2]
  have hs' (i j : Fin 3) : A j i = A i j := congrFun (congrFun hs i) j
  have hc : c ≠ 0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    have h2 := congrFun hz 2
    have h3 := congrFun hz 3
    have h4 := congrFun hz 4
    have h5 := congrFun hz 5
    norm_num [c] at h0 h1 h2 h3 h4 h5
    have h10 : A 1 0 = 0 := (hs' 0 1).trans h3
    have h20 : A 2 0 = 0 := (hs' 0 2).trans h4
    have h21 : A 2 1 = 0 := (hs' 1 2).trans h5
    have hA : A = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5 |
          exact h10 | exact h20 | exact h21
    exact ha (by rw [hA, Matrix.det_zero])
  apply pascal p c hc
  intro i
  have h := hp i
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_succ] at h ⊢
  norm_num [veronese, c] at h ⊢
  rw [hs' 0 1, hs' 0 2, hs' 1 2] at h
  linear_combination h
end HOLLightPort.Pascal

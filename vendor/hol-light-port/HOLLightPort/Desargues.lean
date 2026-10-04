/- Modified for the ClassicalTheorems project on 2026-10-03: manually re-formalized HOL Light’s homogeneous-coordinate argument in Lean; see upstream.json for its pinned source. -/
/-
Copyright (c) University of Cambridge 1998.
Copyright (c) John Harrison and others 1998-2012.
Lean adaptation: ClassicalTheorems contributors, 2026.
Distributed under the BSD-2-Clause terms in LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
namespace HOLLightPort.Desargues
variable {K : Type*} [Field K]
def cross (v w : Fin 3 → K) : Fin 3 → K :=
  ![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0]
def meets (a b : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  ![cross (cross (a 0) (a 1)) (cross (b 0) (b 1)),
    cross (cross (a 1) (a 2)) (cross (b 1) (b 2)),
    cross (cross (a 2) (a 0)) (cross (b 2) (b 0))]
theorem certificate (a b : Matrix (Fin 3) (Fin 3) K) :
    (meets a b).det = a.det * b.det * Matrix.det (fun i => cross (a i) (b i)) := by
  simp only [Matrix.det_fin_three]
  norm_num [meets, cross]
  ring

/-- Perspective triangles have their corresponding side intersections on one projective line. -/
theorem desargues (a b : Matrix (Fin 3) (Fin 3) K) (o : Fin 3 → K)
    (ho : o ≠ 0) (hp : ∀ i, dotProduct (cross (a i) (b i)) o = 0) :
    ∃ line ≠ (0 : Fin 3 → K), ∀ i, dotProduct (meets a b i) line = 0 := by
  have hconn : Matrix.det (fun i => cross (a i) (b i)) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨o, ho, funext hp⟩
  have hm : (meets a b).det = 0 := by rw [certificate, hconn, mul_zero]
  obtain ⟨line, hline, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hm
  exact ⟨line, hline, fun i => congrFun hmul i⟩

/-- The converse for two noncollinear triangles. -/
theorem desargues_converse (a b : Matrix (Fin 3) (Fin 3) K)
    (ha : a.det ≠ 0) (hb : b.det ≠ 0) (line : Fin 3 → K) (hl : line ≠ 0)
    (hp : ∀ i, dotProduct (meets a b i) line = 0) :
    ∃ o ≠ (0 : Fin 3 → K), ∀ i, dotProduct (cross (a i) (b i)) o = 0 := by
  have hm : (meets a b).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨line, hl, funext hp⟩
  rw [certificate] at hm
  have hc : Matrix.det (fun i => cross (a i) (b i)) = 0 :=
    (mul_eq_zero.mp hm).resolve_left (mul_ne_zero ha hb)
  obtain ⟨o, ho, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hc
  exact ⟨o, ho, fun i => congrFun hmul i⟩
end HOLLightPort.Desargues

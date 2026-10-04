/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Schoenflies.Plane
import Mathlib.Tactic.Ring

/-! Heron's algebraic identity in Euclidean coordinates, including degenerate triangles.
This module is independent of the Jordan-domain and Green developments. -/
noncomputable section
namespace ClassicalTheorems

private theorem dist_sq_coords (a b : Schoenflies.Plane) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
  simp [Fin.sum_univ_two]

/-- The semiperimeter product is the square of half the oriented area determinant. -/
theorem heron_product_eq_det_sq (a b c : Schoenflies.Plane) :
    let x := dist a b
    let y := dist b c
    let z := dist c a
    let s := (x + y + z) / 2
    s * (s - x) * (s - y) * (s - z) =
      (Schoenflies.Plane.det (b - a) (c - a) / 2)^2 := by
  dsimp
  have halg (x y z : ℝ) :
      ((x+y+z)/2) * ((x+y+z)/2-x) * ((x+y+z)/2-y) * ((x+y+z)/2-z) =
        (2*x^2*y^2 + 2*y^2*z^2 + 2*z^2*x^2 - (x^2)^2 - (y^2)^2 - (z^2)^2)/16 := by
    ring
  rw [halg, dist_sq_coords, dist_sq_coords, dist_sq_coords]
  simp only [Schoenflies.Plane.det, PiLp.sub_apply]
  ring

/-- The algebraic side-length identity, also valid for collinear vertices. -/
theorem heron_det (a b c : Schoenflies.Plane) :
    let x := dist a b
    let y := dist b c
    let z := dist c a
    let s := (x + y + z) / 2
    Real.sqrt (s * (s - x) * (s - y) * (s - z)) =
      |Schoenflies.Plane.det (b - a) (c - a)| / 2 := by
  dsimp
  rw [heron_product_eq_det_sq, Real.sqrt_sq_eq_abs, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

end ClassicalTheorems
#check_upstream ClassicalTheorems.heron_product_eq_det_sq
#check_upstream ClassicalTheorems.heron_det

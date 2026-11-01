/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Heron
import Mathlib.Tactic.NormNum

/-!
# A geometric regression example for Heron's formula

The translated triangle (2, -1), (5, -1), (2, 3) has side lengths 3, 5, 4
and enclosed Lebesgue area 6. Both vertex orders must give positive area.
These examples apply the public geometric theorem to the three actual segments;
they do not supply an area hypothesis or replace the area with a determinant.
-/

noncomputable section
open Set MeasureTheory

namespace ClassicalTheoremsTest.Triangle

private abbrev a : Schoenflies.Plane := Schoenflies.Plane.mk 2 (-1)
private abbrev b : Schoenflies.Plane := Schoenflies.Plane.mk 5 (-1)
private abbrev c : Schoenflies.Plane := Schoenflies.Plane.mk 2 3

private theorem side_lengths : dist a b = 3 ∧ dist b c = 5 ∧ dist c a = 4 := by
  norm_num [a, b, c, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq]

/-- Counterclockwise vertices enclose area 6, computed from Euclidean side lengths. -/
theorem counterclockwise_area :
    (volume (Schoenflies.inside
      (segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a))).toReal = 6 := by
  have h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0 := by
    norm_num [Schoenflies.Plane.det, a, b, c, PiLp.sub_apply]
  rw [ClassicalTheorems.heron_area a b c h]
  norm_num [side_lengths.1, side_lengths.2.1, side_lengths.2.2]

/-- Reversing the vertices preserves the positive geometric area. -/
theorem clockwise_area :
    (volume (Schoenflies.inside
      (segment ℝ a c ∪ segment ℝ c b ∪ segment ℝ b a))).toReal = 6 := by
  have h : Schoenflies.Plane.det (c - a) (b - a) ≠ 0 := by
    norm_num [Schoenflies.Plane.det, a, b, c, PiLp.sub_apply]
  rw [ClassicalTheorems.heron_area a c b h]
  rw [dist_comm a c, dist_comm c b, dist_comm b a]
  norm_num [side_lengths.1, side_lengths.2.1, side_lengths.2.2]

/-- A third vertex on the same horizontal line fails the geometric theorem's hypothesis. -/
theorem collinear_rejected :
    ¬ Schoenflies.Plane.det (b - a) (Schoenflies.Plane.mk 8 (-1) - a) ≠ 0 := by
  norm_num [Schoenflies.Plane.det, a, b, PiLp.sub_apply]

#check_upstream counterclockwise_area
#check_upstream clockwise_area
#check_upstream collinear_rejected

end ClassicalTheoremsTest.Triangle

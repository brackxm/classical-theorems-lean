/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Elementary sign consequences shared by oriented integral identities. -/
namespace ClassicalTheorems

/-- A positive value selects the positive orientation of a nonzero signed quantity. -/
theorem orientation_eq_true_of_positive {orientation : Bool} {value magnitude : ℝ}
    (hMagnitude : 0 < magnitude)
    (hSigned : value = if orientation then magnitude else -magnitude)
    (hPositive : value = magnitude) : orientation = true := by
  cases orientation with
  | false =>
      simp only [Bool.false_eq_true, ite_false] at hSigned
      linarith
  | true => rfl

/-- Multiplication by either orientation sign preserves absolute value. -/
theorem abs_eq_of_orientation_mul (orientation : Bool) {a b : ℝ}
    (h : a = (if orientation then 1 else -1) * b) : |a| = |b| := by
  rw [h]
  cases orientation <;> simp

end ClassicalTheorems
#check_upstream ClassicalTheorems.orientation_eq_true_of_positive
#check_upstream ClassicalTheorems.abs_eq_of_orientation_mul

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolytopeEulerBound

/-! The algebraic filling property of connected two-endpoint incidence systems.
Over 𝔽₂, their edge boundaries are precisely the coefficient vectors with
zero total sum. This will be applied inside descending vertex figures. -/

noncomputable section
open Classical
namespace ClassicalTheorems.Progress.Euler

/-- The total coefficient of a finite chain. -/
def coefficientSum {α : Type*} [Fintype α] : (α → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun f := ∑ a, f a
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

/-- In a connected incidence system with two objects in each row, the
boundaries of row chains are exactly the object chains of zero total sum. -/
theorem incidence_transpose_range {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : β → α → Prop)
    (hpair : ∀ e, ∃ x y, x ≠ y ∧ ∀ v, r e v ↔ v = x ∨ v = y)
    (hconn : ∀ f : α → ZMod 2,
      (∀ e x y, r e x → r e y → f x = f y) → ∀ x y, f x = f y) :
    LinearMap.range (incidenceMatrix r).transpose.mulVecLin =
      LinearMap.ker (coefficientSum (α := α)) := by
  have hle : LinearMap.range (incidenceMatrix r).transpose.mulVecLin ≤
      LinearMap.ker (coefficientSum (α := α)) := by
    rintro f ⟨c, rfl⟩
    change (∑ a, ∑ b, incidenceMatrix r b a * c b) = 0
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b hb
    have hrow : (∑ a, incidenceMatrix r b a) = 0 := by
      obtain ⟨x, y, hxy, hr⟩ := hpair b
      have hp := incidence_mulVec_pair r b hxy hr (fun _ => (1 : ZMod 2))
      simpa [Matrix.mulVec, dotProduct, CharTwo.add_self_eq_zero] using hp
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hsurj : Function.Surjective (coefficientSum (α := α)) := by
    intro c
    refine ⟨Pi.single (Classical.arbitrary α) c, ?_⟩
    simp [coefficientSum]
  have hnull := (coefficientSum (α := α)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hnull
  have hrank := incidence_rank r hpair hconn
  apply Submodule.eq_of_le_of_finrank_le hle
  have htranspose := Matrix.rank_transpose (incidenceMatrix r)
  change Module.finrank (ZMod 2) (LinearMap.range (incidenceMatrix r).transpose.mulVecLin) =
    (incidenceMatrix r).rank at htranspose
  omega

/-- Every even chain in a connected two-endpoint incidence system can be
filled by a chain of the system's rows. -/
theorem incidence_fill_even {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : β → α → Prop)
    (hpair : ∀ e, ∃ x y, x ≠ y ∧ ∀ v, r e v ↔ v = x ∨ v = y)
    (hconn : ∀ f : α → ZMod 2,
      (∀ e x y, r e x → r e y → f x = f y) → ∀ x y, f x = f y)
    (z : α → ZMod 2) (hz : ∑ a, z a = 0) :
    ∃ c : β → ZMod 2, (incidenceMatrix r).transpose.mulVec c = z := by
  have hker : z ∈ LinearMap.ker (coefficientSum (α := α)) := hz
  rw [← incidence_transpose_range r hpair hconn] at hker
  exact hker

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.incidence_fill_even

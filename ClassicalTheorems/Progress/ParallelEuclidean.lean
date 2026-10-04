/-
Upstream HOL Light:
Copyright (c) University of Cambridge 1998.
Copyright (c) John Harrison and others 1998-2012.

Lean adaptation:
Copyright 2026 Michael Brackx
SPDX-License-Identifier: BSD-2-Clause

Manual mathematical adaptation of the model argument in John Harrison’s HOL Light
Multivariate/tarski.ml and 100/independence.ml (with credit to Tim Makarios).
The Lean proofs, including the Lorentz-coordinate construction, are verified anew.
See NOTICE and vendor/hol-light-port/LICENSE for attribution and license terms.
-/
import ClassicalTheorems.Progress.ParallelAffine
import ClassicalTheorems.Statements.Tarski

/-! The complete Euclidean model for the positive half of parallel-postulate independence. -/

namespace ClassicalTheorems.Progress.Parallel

open AffineMap Set Module
open scoped RealInnerProductSpace

/-- Squared Euclidean distance in real coordinates. -/
theorem dist_sq (a b : ℂ) :
    dist a b ^ 2 = (a.re - b.re)^2 + (a.im - b.im)^2 := by
  rw [dist_eq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, pow_two]

/-- The squared distance to an affine extension is determined by three distances. -/
theorem extension_dist_sq (a b d : ℂ) (r : ℝ) :
    dist (lineMap a b r) d ^ 2 =
      (1-r) * dist a d ^ 2 + r * dist b d ^ 2 - r * (1-r) * dist a b ^ 2 := by
  simp only [dist_sq, lineMap_apply_module, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- The five-segment axiom, without an isometry-existence assumption. -/
theorem five_segment (a b c d a' b' c' d' : ℂ) (hab : a ≠ b)
    (hc : Wbtw ℝ a b c) (hc' : Wbtw ℝ a' b' c')
    (h1 : dist a b = dist a' b') (h2 : dist b c = dist b' c')
    (h3 : dist a d = dist a' d') (h4 : dist b d = dist b' d') :
    dist c d = dist c' d' := by
  have hab' : a' ≠ b' := by intro he; simp [he] at h1; exact hab h1
  rcases hc.right_mem_image_Ici_of_left_ne hab with ⟨r, hr, hrc⟩
  rcases hc'.right_mem_image_Ici_of_left_ne hab' with ⟨s, hs, hsc⟩
  change 1 ≤ r at hr
  change 1 ≤ s at hs
  have hsum := hc.dist_add_dist
  have hsum' := hc'.dist_add_dist
  have hac : dist a c = dist a' c' := by linarith
  rw [← hrc, ← hsc, dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r),
    abs_of_nonneg (by linarith : 0 ≤ s), ← h1] at hac
  have hrs : r = s := (mul_right_cancel₀ (ne_of_gt (dist_pos.mpr hab))) hac
  have hsq : dist c d ^ 2 = dist c' d' ^ 2 := by
    rw [← hrc, ← hsc, extension_dist_sq, extension_dist_sq, hrs, h1, h3, h4]
  nlinarith [dist_nonneg (x := c) (y := d), dist_nonneg (x := c') (y := d')]

/-- Segment construction on the ray from `q` through `a`. -/
theorem segment_construction (a b c q : ℂ) :
    ∃ x : ℂ, Wbtw ℝ q a x ∧ dist a x = dist b c := by
  by_cases hqa : q = a
  · subst q
    refine ⟨a + (dist b c : ℂ), wbtw_self_left _ _ _, ?_⟩
    simp [dist_eq_norm]
  have hpos : 0 < dist q a := dist_pos.mpr hqa
  let r := 1 + dist b c / dist q a
  have hquot : 0 ≤ dist b c / dist q a := div_nonneg dist_nonneg hpos.le
  have hr : 1 ≤ r := by dsimp [r]; linarith
  refine ⟨lineMap q a r,
    wbtw_iff_left_eq_or_right_mem_image_Ici.mpr (.inr ⟨r, hr, rfl⟩), ?_⟩
  rw [dist_comm, dist_lineMap_right, Real.norm_eq_abs,
    abs_of_nonpos (by dsimp [r]; linarith)]
  dsimp [r]
  field_simp
  ring

/-- Three points equidistant from distinct points lie on their perpendicular bisector. -/
theorem equidistant_collinear (p q a b c : ℂ) (hpq : p ≠ q)
    (ha : dist a p = dist a q) (hb : dist b p = dist b q)
    (hc : dist c p = dist c q) : Collinear ℝ ({a,b,c} : Set ℂ) := by
  have hperp : ∀ x y : ℂ, dist x p = dist x q → dist y p = dist y q →
      inner ℝ (p-q) (x-y) = 0 := by
    intro x y hx hy
    have hx' : dist p x = dist q x := by simpa only [dist_comm] using hx
    have hy' : dist p y = dist q y := by simpa only [dist_comm] using hy
    calc inner ℝ (p-q) (x-y) = inner ℝ (y-x) (q-p) := by
           rw [show y-x = -(x-y) by abel, show q-p = -(p-q) by abel,
             inner_neg_neg, real_inner_comm]
         _ = 0 := EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq hx' hy'
  let W : Submodule ℝ ℂ := (ℝ ∙ (p-q))ᗮ
  have : Fact (finrank ℝ ℂ = 1+1) := ⟨Complex.finrank_real_complex⟩
  have hdim : finrank ℝ W = 1 :=
    Submodule.finrank_orthogonal_span_singleton (sub_ne_zero.mpr hpq)
  have hm : ∀ x ∈ ({a,b,c} : Set ℂ), (a -ᵥ x : ℂ) ∈ W := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with hxa | hxb | hxc
    · subst x; simp
    · subst x; exact hperp a b ha hb
    · subst x; exact hperp a c ha hc
  have hspan : vectorSpan ℝ ({a,b,c} : Set ℂ) ≤ W := by
    rw [vectorSpan_eq_span_vsub_set_left ℝ (by simp : a ∈ ({a,b,c} : Set ℂ)),
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hm x hx
  rw [collinear_iff_finrank_le_one]
  exact (Submodule.finrank_mono hspan).trans hdim.le

/-- The three standard coordinate points witness dimension at least two. -/
theorem lower_dimension : ∃ a b c : ℂ,
    ¬Wbtw ℝ a b c ∧ ¬Wbtw ℝ b c a ∧ ¬Wbtw ℝ c a b := by
  refine ⟨0, 1, Complex.I, ?_, ?_, ?_⟩
  all_goals
    intro h
    rcases (between_iff _ _ _).mp h with ⟨t, ht0, ht1, he⟩
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    simp only [Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hr hi
    nlinarith

/-- Real coordinate plane with metric congruence and affine betweenness. -/
noncomputable def euclideanPlane : Statements.Geometry.NeutralPlane where
  Point := ℂ
  between := Wbtw ℝ
  congruent a b c d := dist a b = dist c d
  congruence_reversal := dist_comm
  congruence_transitivity := fun _ _ _ _ _ _ h1 h2 ↦ h1.symm.trans h2
  congruence_identity := fun a b c h ↦ dist_eq_zero.mp (by simpa using h)
  segment_construction := segment_construction
  five_segment := five_segment
  betweenness_identity := fun _ _ h ↦ ((wbtw_self_iff ℝ).mp h).symm
  inner_pasch := inner_pasch
  lower_dimension := lower_dimension
  upper_dimension := fun a b c p q hpq ha hb hc ↦
    (equidistant_collinear p q a b c hpq ha hb hc).wbtw_or_wbtw_or_wbtw
  continuity := continuity

/-- The entire positive existential in parallel-postulate independence. -/
theorem euclidean_model : ∃ plane : Statements.Geometry.NeutralPlane,
    plane.ParallelPostulate := by
  exact ⟨euclideanPlane, euclidean_axiom⟩

end ClassicalTheorems.Progress.Parallel

#check_upstream ClassicalTheorems.Progress.Parallel.five_segment
#check_upstream ClassicalTheorems.Progress.Parallel.euclideanPlane
#check_upstream ClassicalTheorems.Progress.Parallel.euclidean_model

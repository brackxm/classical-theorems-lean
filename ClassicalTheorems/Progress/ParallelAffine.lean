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
import ClassicalTheorems.Audit
import Mathlib.Analysis.Convex.StrictConvexBetween
import Mathlib.Analysis.Complex.Basic
import Mathlib

/-! Affine betweenness lemmas for the two models used in parallel-postulate independence. -/

namespace ClassicalTheorems.Progress.Parallel

open AffineMap Set

/-- Coordinate form of weak betweenness in the real complex plane. -/
theorem between_iff (a b c : ℂ) :
    Wbtw ℝ a b c ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ b = (1 - t) • a + t • c := by
  change (∃ t ∈ Icc (0 : ℝ) 1, lineMap a c t = b) ↔ _
  simp only [mem_Icc, lineMap_apply_module]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, he⟩
    exact ⟨t, h0, h1, he.symm⟩
  · rintro ⟨t, h0, h1, he⟩
    exact ⟨t, ⟨h0, h1⟩, he.symm⟩

/-- Inner Pasch, proved by intersecting the two affine segments. -/
theorem inner_pasch (a b c p q : ℂ) (hp : Wbtw ℝ a p c) (hq : Wbtw ℝ b q c) :
    ∃ x : ℂ, Wbtw ℝ p x b ∧ Wbtw ℝ q x a := by
  rcases (between_iff a p c).mp hp with ⟨s, hs0, hs1, rfl⟩
  rcases (between_iff b q c).mp hq with ⟨t, ht0, ht1, rfl⟩
  by_cases hz : s + t - s * t = 0
  · have hprod : 0 ≤ s * (1 - t) := mul_nonneg hs0 (sub_nonneg.mpr ht1)
    have ht : t = 0 := by nlinarith
    have hs : s = 0 := by nlinarith
    subst s; subst t
    simp only [sub_zero, one_smul, zero_smul, add_zero]
    exact ⟨a, wbtw_self_left _ _ _, wbtw_self_right _ _ _⟩
  have hd : 0 < s + t - s * t := by
    have := mul_nonneg hs0 (sub_nonneg.mpr ht1)
    exact lt_of_le_of_ne (by nlinarith) (Ne.symm hz)
  let u := s * (1 - t) / (s + t - s * t)
  let v := t * (1 - s) / (s + t - s * t)
  have hu0 : 0 ≤ u := div_nonneg (mul_nonneg hs0 (sub_nonneg.mpr ht1)) hd.le
  have hu1 : u ≤ 1 := by dsimp [u]; apply (div_le_one hd).mpr; nlinarith
  have hv0 : 0 ≤ v := div_nonneg (mul_nonneg ht0 (sub_nonneg.mpr hs1)) hd.le
  have hv1 : v ≤ 1 := by dsimp [v]; apply (div_le_one hd).mpr; nlinarith
  refine ⟨(1 - u) • ((1 - s) • a + s • c) + u • b,
    (between_iff _ _ _).mpr ⟨u, hu0, hu1, rfl⟩,
    (between_iff _ _ _).mpr ⟨v, hv0, hv1, ?_⟩⟩
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
    dsimp [u, v] <;> field_simp [hz] <;> ring

/-- Tarski's Euclidean axiom in the full affine plane. -/
theorem euclidean_axiom (a b c d t : ℂ)
    (hadt : Wbtw ℝ a d t) (hbdc : Wbtw ℝ b d c) (had : a ≠ d) :
    ∃ x y : ℂ, Wbtw ℝ a b x ∧ Wbtw ℝ a c y ∧ Wbtw ℝ x t y := by
  rcases (between_iff a d t).mp hadt with ⟨u, hu0, hu1, hdu⟩
  rcases (between_iff b d c).mp hbdc with ⟨v, hv0, hv1, hdv⟩
  have hu : u ≠ 0 := by
    intro hz
    simp [hz] at hdu
    exact had hdu.symm
  let x := u⁻¹ • b + (1 - u⁻¹) • a
  let y := u⁻¹ • c + (1 - u⁻¹) • a
  have hb : b = (1 - u) • a + u • x := by
    dsimp only [x]
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp [hu] <;> ring
  have hc : c = (1 - u) • a + u • y := by
    dsimp only [y]
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp [hu] <;> ring
  have ht : t = (1 - v) • x + v • y := by
    have he : (1 - u) • a + u • t = (1 - v) • b + v • c := hdu.symm.trans hdv
    apply (smul_right_injective ℂ hu)
    calc u • t = (1 - v) • b + v • c - (1 - u) • a := by rw [← he]; abel
         _ = u • ((1 - v) • (u⁻¹ • b + (1 - u⁻¹) • a) +
               v • (u⁻¹ • c + (1 - u⁻¹) • a)) := by
           apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul] <;> field_simp [hu] <;> ring
  exact ⟨x, y, (between_iff _ _ _).mpr ⟨u, hu0, hu1, hb⟩,
    (between_iff _ _ _).mpr ⟨u, hu0, hu1, hc⟩,
    (between_iff _ _ _).mpr ⟨v, hv0, hv1, ht⟩⟩

/-- Points on a common segment are ordered by distance from its left endpoint. -/
theorem between_of_distance_order (a x b y : ℂ)
    (hx : Wbtw ℝ a x y) (hb : Wbtw ℝ a b y) (hle : dist a x ≤ dist a b) :
    Wbtw ℝ x b y := by
  by_cases hay : a = y
  · subst y
    have hx' := (wbtw_self_iff (R := ℝ)).mp hx
    have hb' := (wbtw_self_iff (R := ℝ)).mp hb
    subst x; subst b; exact wbtw_self_left _ _ _
  rcases hx with ⟨r, hr, rfl⟩
  rcases hb with ⟨s, hs, rfl⟩
  have hdist : 0 < dist a y := dist_pos.mpr hay
  rw [dist_left_lineMap, dist_left_lineMap, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hr.1, abs_of_nonneg hs.1] at hle
  have hrs : r ≤ s := (mul_le_mul_iff_left₀ hdist).mp hle
  simpa using (Wbtw.of_le_of_le hrs hs.2).map (lineMap a y)

theorem compact_segment (a b : ℂ) : IsCompact (segment ℝ a b) := by
  rw [segment_eq_image_lineMap]
  exact isCompact_Icc.image lineMap_continuous

/-- Dedekind continuity for arbitrary subsets of the real plane.
The separating point maximizes distance on the compact closure of the lower set. -/
theorem continuity (X Y : Set ℂ)
    (h : ∃ a, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ a x y) :
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, Wbtw ℝ x b y := by
  classical
  rcases h with ⟨a, h⟩
  rcases X.eq_empty_or_nonempty with rfl | hX
  · exact ⟨a, by simp⟩
  rcases Y.eq_empty_or_nonempty with rfl | hY
  · exact ⟨a, by simp⟩
  rcases hY with ⟨y0, hy0⟩
  have hsub : ∀ y ∈ Y, closure X ⊆ segment ℝ a y := by
    intro y hy
    exact closure_minimal (fun x hx ↦ (h x hx y hy).mem_segment)
      (compact_segment a y).isClosed
  have hcompact : IsCompact (closure X) :=
    (compact_segment a y0).of_isClosed_subset isClosed_closure (hsub y0 hy0)
  rcases hcompact.exists_isMaxOn hX.closure (continuous_const.dist continuous_id).continuousOn
    with ⟨b, hb, hmax⟩
  refine ⟨b, fun x hx y hy ↦ ?_⟩
  exact between_of_distance_order a x b y (h x hx y hy)
    (mem_segment_iff_wbtw.mp (hsub y hy hb)) (hmax (subset_closure hx))

end ClassicalTheorems.Progress.Parallel

#check_upstream ClassicalTheorems.Progress.Parallel.inner_pasch
#check_upstream ClassicalTheorems.Progress.Parallel.euclidean_axiom
#check_upstream ClassicalTheorems.Progress.Parallel.continuity

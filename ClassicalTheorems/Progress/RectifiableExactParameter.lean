/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricRectifiable

/-! Exact Lipschitz parametrization of a rectifiable Jordan curve. Simplicity
makes accumulated variation strictly increasing, so no ε is required. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- Simplicity makes accumulated length strictly increase, including at the
common endpoint of a closed Jordan parametrization. -/
theorem jordan_variation_strict (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hsimple : InjOn γ (Ico (0 : ℝ) 1)) :
    StrictMonoOn (variationOnFromTo γ (Icc (0 : ℝ) 1) 0) (Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  let z := (x + y) / 2
  have hxz : x < z := by dsimp only [z]; linarith
  have hzy : z < y := by dsimp only [z]; linarith
  have hz : z ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hy.2]⟩
  have hne : γ x ≠ γ z := by
    intro he
    have h := hsimple ⟨hx.1, by linarith [hy.2]⟩ ⟨hz.1, by linarith [hy.2]⟩ he
    exact hxz.ne h
  have hv := dist_le_variation_increment γ hBV hx hz hxz.le
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) hz hy hzy.le
  have hp := dist_pos.mpr hne
  linarith

/-- An exact length-bounded Lipschitz representative of a rectifiable simple
curve, preserving its ordered image by an interval automorphism. -/
theorem jordan_exact_lipschitz_parameter (γ : ℝ → Point)
    (hcont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hsimple : InjOn γ (Ico (0 : ℝ) 1)) :
    ∃ δ : ℝ → Point, LipschitzWith
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal.toNNReal δ ∧
      ∃ e : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
        ∀ t : Icc (0 : ℝ) 1, δ t = γ (e t) := by
  let ℓ := variationOnFromTo γ (Icc (0 : ℝ) 1) 0
  let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
  have hℓstrict := jordan_variation_strict γ hBV hsimple
  have hℓ1 : ℓ 1 = L := by
    dsimp only [ℓ, L]
    rw [variationOnFromTo.eq_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1), inter_self]
  have hLp : 0 < L := by
    have h := hℓstrict (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) < 1)
    change ℓ 0 < ℓ 1 at h
    simpa only [ℓ, variationOnFromTo.self, hℓ1] using h
  have hℓc : ContinuousOn ℓ (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hBV.continuousWithinAt_variationOnFromTo_iff
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht).mpr (hcont t ht)
  have hℓmono : MonotoneOn ℓ (Icc (0 : ℝ) 1) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  let r := fun t => ℓ t / L
  have hrc : ContinuousOn r (Icc (0 : ℝ) 1) :=
    hℓc.div_const _
  have hrstrict : StrictMonoOn r (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply (div_lt_div_iff_of_pos_right hLp).mpr
    exact hℓstrict hx hy hxy
  have hr0 : r 0 = 0 := by simp [r, ℓ, variationOnFromTo.self]
  have hr1 : r 1 = 1 := by
    have hℓ1 : ℓ 1 = L := by
      dsimp only [ℓ, L]
      rw [variationOnFromTo.eq_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1), inter_self]
    simp only [r, hℓ1]
    exact div_self hLp.ne'
  have hrimage : r '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hrc.image_Icc_of_monotoneOn (by norm_num) hrstrict.monotoneOn, hr0, hr1]
  let e : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1 :=
    (hrstrict.orderIso r (Icc (0 : ℝ) 1)).trans (Set.orderIsoOfEq _ _ hrimage)
  have her (t : Icc (0 : ℝ) 1) : (e t : ℝ) = r t := rfl
  have heinverse (t : Icc (0 : ℝ) 1) : r (e.symm t) = t := by
    rw [← her, e.apply_symm_apply]
  let q := fun t : Icc (0 : ℝ) 1 => γ (e.symm t)
  have hqle (s t : Icc (0 : ℝ) 1) (hst : s ≤ t) :
      dist (q s) (q t) ≤ L * dist s t := by
    have hxy : (e.symm s : ℝ) ≤ e.symm t := e.symm.monotone hst
    have hv := dist_le_variation_increment γ hBV (e.symm s).property (e.symm t).property hxy
    have hs : ℓ (e.symm s) = (s : ℝ) * L := by
      have h := heinverse s
      dsimp only [r] at h
      exact (div_eq_iff hLp.ne').mp h
    have ht : ℓ (e.symm t) = (t : ℝ) * L := by
      have h := heinverse t
      dsimp only [r] at h
      exact (div_eq_iff hLp.ne').mp h
    change dist (γ (e.symm s)) (γ (e.symm t)) ≤ L * dist (s : ℝ) (t : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst)), neg_sub]
    change dist (γ (e.symm s)) (γ (e.symm t)) ≤ ℓ (e.symm t) - ℓ (e.symm s) at hv
    nlinarith
  have hq : LipschitzWith L.toNNReal q := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal _ hLp.le]
    rcases le_total s t with h | h
    · exact hqle s t h
    · simpa only [dist_comm] using hqle t s h
  let δ := q ∘ projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1)
  have hδ : LipschitzWith L.toNNReal δ := by
    simpa only [mul_one] using hq.comp (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))
  refine ⟨δ, hδ, e.symm, ?_⟩
  intro t
  dsimp only [δ, Function.comp_apply]
  rw [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) t.property]


end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_exact_lipschitz_parameter

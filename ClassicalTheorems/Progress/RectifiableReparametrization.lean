/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricACArea
import MovingSofa.Curve.Jordan.Winding
import Mathlib.Topology.Order.MonotoneContinuity

/-! Lipschitz reparametrization of a continuous rectifiable path, with an
arbitrarily small excess in the Lipschitz constant. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

theorem dist_le_variation_increment (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    dist (γ x) (γ y) ≤ variationOnFromTo γ (Icc (0 : ℝ) 1) 0 y -
      variationOnFromTo γ (Icc (0 : ℝ) 1) 0 x := by
  have hv : dist (γ x) (γ y) ≤ variationOnFromTo γ (Icc (0 : ℝ) 1) x y := by
    rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
    apply ENNReal.toReal_mono (hBV.locallyBoundedVariationOn x y hx hy)
    exact eVariationOn.edist_le γ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  have ha := variationOnFromTo.add hBV.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) hx hy
  linarith

/-- For each ε>0, a continuous finite-variation path has the same ordered image
as a globally Lipschitz path with constant at most total length + ε. -/
theorem bv_approx_lipschitz_parameter (γ : ℝ → Point)
    (hcont : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ → Point, LipschitzWith
      ((eVariationOn γ (Icc (0 : ℝ) 1)).toReal + ε).toNNReal δ ∧
      ∃ e : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1,
        ∀ t : Icc (0 : ℝ) 1, δ t = γ (e t) := by
  let ℓ := variationOnFromTo γ (Icc (0 : ℝ) 1) 0
  let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
  have hLp : 0 < L + ε := by dsimp only [L]; positivity
  have hℓc : ContinuousOn ℓ (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hBV.continuousWithinAt_variationOnFromTo_iff
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht).mpr (hcont t ht)
  have hℓmono : MonotoneOn ℓ (Icc (0 : ℝ) 1) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  let r := fun t => (ℓ t + ε * t) / (L + ε)
  have hrc : ContinuousOn r (Icc (0 : ℝ) 1) :=
    (hℓc.add (continuousOn_const.mul continuousOn_id)).div_const _
  have hrstrict : StrictMonoOn r (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    apply (div_lt_div_iff_of_pos_right hLp).mpr
    have hm := hℓmono hx hy hxy.le
    nlinarith
  have hr0 : r 0 = 0 := by simp [r, ℓ, variationOnFromTo.self]
  have hr1 : r 1 = 1 := by
    have hℓ1 : ℓ 1 = L := by
      dsimp only [ℓ, L]
      rw [variationOnFromTo.eq_of_le _ _ (by norm_num : (0 : ℝ) ≤ 1), inter_self]
    simp only [r, hℓ1, mul_one]
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
      dist (q s) (q t) ≤ (L + ε) * dist s t := by
    have hxy : (e.symm s : ℝ) ≤ e.symm t := e.symm.monotone hst
    have hv := dist_le_variation_increment γ hBV (e.symm s).property (e.symm t).property hxy
    have hs : ℓ (e.symm s) + ε * (e.symm s : ℝ) = (s : ℝ) * (L + ε) := by
      have h := heinverse s
      dsimp only [r] at h
      exact (div_eq_iff hLp.ne').mp h
    have ht : ℓ (e.symm t) + ε * (e.symm t : ℝ) = (t : ℝ) * (L + ε) := by
      have h := heinverse t
      dsimp only [r] at h
      exact (div_eq_iff hLp.ne').mp h
    change dist (γ (e.symm s)) (γ (e.symm t)) ≤ (L + ε) * dist (s : ℝ) (t : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hst)), neg_sub]
    change dist (γ (e.symm s)) (γ (e.symm t)) ≤ ℓ (e.symm t) - ℓ (e.symm s) at hv
    nlinarith
  have hq : LipschitzWith (L + ε).toNNReal q := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal _ hLp.le]
    rcases le_total s t with h | h
    · exact hqle s t h
    · simpa only [dist_comm] using hqle t s h
  let δ := q ∘ projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1)
  have hδ : LipschitzWith (L + ε).toNNReal δ := by
    simpa only [mul_one] using hq.comp (LipschitzWith.projIcc (by norm_num : (0 : ℝ) ≤ 1))
  refine ⟨δ, hδ, e.symm, ?_⟩
  intro t
  dsimp only [δ, Function.comp_apply]
  rw [projIcc_of_mem (by norm_num : (0 : ℝ) ≤ 1) t.property]

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.bv_approx_lipschitz_parameter

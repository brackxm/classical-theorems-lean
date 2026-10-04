/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RectifiableReparametrization

/-! The sharp geometric isoperimetric inequality for all continuous rectifiable
Jordan parametrizations. Perimeter is total variation. Circle rigidity is proved
in `IsoperimetricRectifiableEquality`, and the circle equivalence in `IsoperimetricCircleIff`. -/

noncomputable section
open MeasureTheory Set MovingSofa Filter
open scoped Topology
namespace ClassicalTheorems.Progress.Isoperimetric

/-- Increasing interval automorphisms preserve the dependency's Jordan
orientation, including winding and injectivity away from the common endpoint. -/
theorem oriented_jordan_comp_orderIso (x : Icc (0 : ℝ) 1 → Point) (Γ : Set Point)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true x)
    (e : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true (x ∘ e) := by
  let : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
  have he0 : e ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := e.map_bot
  have he1 : e ⟨1, by norm_num⟩ = ⟨1, by norm_num⟩ := e.map_top
  have hrange : range (x ∘ e) = Γ := by
    rw [← hx.2.2.2.1]
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨e t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨e.symm t, by simp⟩
  refine ⟨hx.1, hx.2.1, hx.2.2.1.comp e.continuous, hrange, ?_, ?_, ?_⟩
  · simpa only [Function.comp_apply, he0, he1] using hx.2.2.2.2.1
  · intro s hs t ht hst
    have hs' : (e s : ℝ) < 1 := by
      change e s < (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)
      rw [← he1]
      exact e.strictMono hs
    have ht' : (e t : ℝ) < 1 := by
      change e t < (⟨1, by norm_num⟩ : Icc (0 : ℝ) 1)
      rw [← he1]
      exact e.strictMono ht
    exact e.injective (hx.2.2.2.2.2.1 hs' ht' hst)
  · intro p hp
    have hw : curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p = 1 := by
      simpa using hx.2.2.2.2.2.2 p hp
    have hlift := exists_curveAngleLift_of_curveWinding_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by rw [hw]; norm_num)
    rw [curveWinding_comp_of_endpoints (by norm_num) (by norm_num) hlift
      e.continuous he0 he1, hw]
    rfl

/-- The sharp bound for a continuous rectifiable Jordan boundary, with arbitrary
parametrization. The perimeter is its finite total variation. -/
theorem jordan_isoperimetric_rectifiable (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 := by
  let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr horiented.2.2.1
  have happrox (ε : ℝ) (hε : 0 < ε) :
      4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤ (L + ε) ^ 2 := by
    obtain ⟨δ, hδ, e, he⟩ := bv_approx_lipschitz_parameter γ hcont hBV ε hε
    have hparam : (fun t : Icc (0 : ℝ) 1 => δ t) = (fun t : Icc (0 : ℝ) 1 => γ t) ∘ e :=
      funext he
    have hOriented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
        (fun t : Icc (0 : ℝ) 1 => δ t) := by
      rw [hparam]
      exact oriented_jordan_comp_orderIso _ Γ horiented e
    have hb := jordan_area_le_lipschitz_bound δ (L + ε).toNNReal hδ Γ hOriented
    have hp : 0 ≤ L + ε := by dsimp only [L]; positivity
    simpa only [Real.coe_toNNReal _ hp] using hb
  have hlim : Tendsto (fun ε : ℝ => (L + ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (L ^ 2)) := by
    have hc : Continuous (fun ε : ℝ => (L + ε) ^ 2) := by fun_prop
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact happrox ε hε

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_comp_orderIso
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_rectifiable

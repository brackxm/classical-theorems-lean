/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricRectifiableEquality
import MovingSofa.ForMathlib.Topology.Order.Interval

/-! Reversing a rectifiable Jordan parametrization preserves perimeter and
the geometric boundary, and exchanges clockwise and counterclockwise winding. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A simple closed path is injective on either half-open parameter interval. -/
theorem jordan_injOn_right_halfopen (x : Icc (0 : ℝ) 1 → Point)
    (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) :
    InjOn x {t | 0 < (t : ℝ)} := by
  intro s hs t ht hst
  have hlt (u : Icc (0 : ℝ) 1) (hu : u ≠ ⟨1, by norm_num⟩) : (u : ℝ) < 1 := by
    exact lt_of_le_of_ne u.property.2 (fun h => hu (Subtype.ext h))
  by_cases hs1 : s = ⟨1, by norm_num⟩
  · subst s
    by_cases ht1 : t = ⟨1, by norm_num⟩
    · exact ht1.symm
    · have h0t := hinj (x₁ := ⟨0, by norm_num⟩) (x₂ := t)
        (by norm_num) (hlt t ht1) (hclosed.trans hst)
      have ht0 := congrArg Subtype.val h0t
      change (0 : ℝ) = (t : ℝ) at ht0
      change 0 < (t : ℝ) at ht
      exfalso
      linarith
  · by_cases ht1 : t = ⟨1, by norm_num⟩
    · subst t
      have hs0 := hinj (x₁ := s) (x₂ := ⟨0, by norm_num⟩)
        (hlt s hs1) (by norm_num) (hst.trans hclosed.symm)
      have hs0' := congrArg Subtype.val hs0
      change (s : ℝ) = 0 at hs0'
      change 0 < (s : ℝ) at hs
      exfalso
      linarith
    · exact hinj (hlt s hs1) (hlt t ht1) hst

/-- Interval reversal exchanges the two orientations of the same Jordan curve. -/
theorem oriented_jordan_reverse (x : Icc (0 : ℝ) 1 → Point) (Γ : Set Point)
    (orientation : Bool)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      Γ orientation x) :
    IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ (!orientation)
      (x ∘ Icc.reverse (by norm_num : (0 : ℝ) ≤ 1)) := by
  let r := Icc.reverse (by norm_num : (0 : ℝ) ≤ 1)
  have hr0 : r ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [r, Icc.reverse]
  have hr1 : r ⟨1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    norm_num [r, Icc.reverse]
  have hrange : range (x ∘ r) = Γ := by
    rw [← hx.2.2.2.1]
    ext p
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨r t, rfl⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨s, hs⟩ := Icc.surjective_reverse (by norm_num : (0 : ℝ) ≤ 1) t
      exact ⟨s, congrArg x hs⟩
  refine ⟨hx.1, hx.2.1, hx.2.2.1.comp (Icc.continuous_reverse _), hrange, ?_, ?_, ?_⟩
  · change x (r ⟨0, by norm_num⟩) = x (r ⟨1, by norm_num⟩)
    rw [hr0, hr1]
    exact hx.2.2.2.2.1.symm
  · intro s hs t ht hst
    have hs' : 0 < (r s : ℝ) := by
      change 0 < 0 + 1 - (s : ℝ)
      change (s : ℝ) < 1 at hs
      linarith
    have ht' : 0 < (r t : ℝ) := by
      change 0 < 0 + 1 - (t : ℝ)
      change (t : ℝ) < 1 at ht
      linarith
    have he := jordan_injOn_right_halfopen x hx.2.2.2.2.1 hx.2.2.2.2.2.1 hs' ht' hst
    exact (Icc.involutive_reverse (by norm_num : (0 : ℝ) ≤ 1)).injective he
  · intro p hp
    have hw := hx.2.2.2.2.2.2 p hp
    have hn : curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p ≠ 0 := by
      rw [hw]
      cases orientation <;> norm_num
    have hlift := exists_curveAngleLift_of_curveWinding_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) hn
    rw [curveWinding_comp_of_reversed_endpoints (by norm_num) (by norm_num)
      hlift (Icc.continuous_reverse _) hr0 hr1, hw]
    cases orientation <;> norm_num

/-- Reversing the parameter preserves total variation on the unit interval. -/
theorem eVariationOn_reverse_unit (γ : ℝ → Point) :
    eVariationOn (fun t => γ (1 - t)) (Icc (0 : ℝ) 1) =
      eVariationOn γ (Icc (0 : ℝ) 1) := by
  have hanti : AntitoneOn (fun t : ℝ => 1 - t) (Icc (0 : ℝ) 1) := by
    intro s _ t _ hst
    linarith
  have himage : (fun t : ℝ => 1 - t) '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      constructor <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      ring
  simpa only [Function.comp_def, himage] using
    eVariationOn.comp_eq_of_antitoneOn γ (fun t : ℝ => 1 - t) hanti

/-- The sharp bound and circle rigidity hold for both Jordan orientations. -/
theorem jordan_isoperimetric_rectifiable_any_orientation (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (orientation : Bool)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 →
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  cases orientation with
  | true =>
      exact ⟨jordan_isoperimetric_rectifiable γ hBV Γ horiented,
        jordan_isoperimetric_equality_rectifiable γ hBV Γ horiented⟩
  | false =>
      let δ : ℝ → Point := fun t => γ (1 - t)
      have hv : eVariationOn δ (Icc (0 : ℝ) 1) = eVariationOn γ (Icc (0 : ℝ) 1) :=
        eVariationOn_reverse_unit γ
      have hδ : BoundedVariationOn δ (Icc (0 : ℝ) 1) := by
        simpa only [BoundedVariationOn, hv] using hBV
      have ho : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
          Γ true (fun t : Icc (0 : ℝ) 1 => δ t) := by
        simpa only [Bool.not_false, Function.comp_def, Icc.reverse, zero_add, δ] using
          oriented_jordan_reverse (fun t : Icc (0 : ℝ) 1 => γ t) Γ false horiented
      simpa only [hv, ClassicalResults.area] using
        And.intro (jordan_isoperimetric_rectifiable δ hδ Γ ho)
          (jordan_isoperimetric_equality_rectifiable δ hδ Γ ho)

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_injOn_right_halfopen
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_reverse
#check_upstream ClassicalTheorems.Progress.Isoperimetric.eVariationOn_reverse_unit
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_rectifiable_any_orientation

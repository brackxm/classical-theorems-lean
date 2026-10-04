/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricInterval
import MovingSofa.Curve.Jordan.Interior
import MovingSofa.Curve.Jordan.WindingLifts

/-! A single interior winding witness determines the orientation everywhere.
The geometric Jordan hypotheses are kept explicit. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The geometric Jordan interior is the complementary component of any of its points. -/
theorem jordanInterior_eq_component {Γ : Set Point} (hΓ : IsJordanCurve Γ)
    {p : Point} (hp : p ∈ jordanInterior Γ) :
    jordanInterior Γ = connectedComponentIn Γᶜ p := by
  obtain ⟨U, V, _, _, _, _, hUb, hVb, _, hcover, _, _, hUc, hVc⟩ := jordan_separation hΓ
  have hpU : p ∈ U := by
    rcases hcover.symm.subset hp.1 with h | h
    · exact h
    · exact False.elim (hVb (hVc p h ▸ hp.2))
  rw [hUc p hpU]
  ext q
  constructor
  · intro hq
    rcases hcover.symm.subset hq.1 with h | h
    · exact h
    · exact False.elim (hVb (hVc q h ▸ hq.2))
  · intro hq
    refine ⟨hcover.subset (Or.inl hq), ?_⟩
    rw [hUc q hq]
    exact hUb

/-- Winding of a continuous closed parametrization is constant throughout the
geometric Jordan interior. No orientation hypothesis is needed. -/
theorem jordan_winding_constant {a b : ℝ} (hab : a ≤ b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {p q : Point} (hp : p ∈ jordanInterior Γ) (hq : q ∈ jordanInterior Γ) :
    curveWinding hab x q = curveWinding hab x p := by
  let U := jordanInterior Γ
  let : PreconnectedSpace U := Subtype.preconnectedSpace (by
    dsimp [U]
    rw [jordanInterior_eq_component hΓ hp]
    exact isPreconnected_connectedComponentIn)
  have hlc : IsLocallyConstant (fun z : U => curveWinding hab x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    have hz : z.val ∉ range x := hrange ▸ z.property.1
    obtain ⟨W, hW, hzW, hWeq⟩ :=
      curveWinding_locally_constant_off_range hab hx hclosed hz
    exact ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hzW,
      fun w hw => hWeq w.val hw⟩
  exact hlc.apply_eq_of_preconnectedSpace ⟨q, hq⟩ ⟨p, hp⟩

/-- A winding value of absolute value one at a single interior point supplies
the complete global Jordan orientation condition. -/
theorem oriented_jordan_of_winding_witness {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b})
    (p : Point) (hp : p ∈ jordanInterior Γ)
    (hw : |curveWinding hab.le x p| = 1) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x := by
  rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1) |>.mp hw with hw | hw
  · refine ⟨true, hab, hΓ, hx, hrange, hclosed, hinj, ?_⟩
    intro q hq
    simpa only [Bool.true_eq, ite_true] using
      (jordan_winding_constant hab.le x Γ hΓ hx hrange hclosed hp hq).trans hw
  · refine ⟨false, hab, hΓ, hx, hrange, hclosed, hinj, ?_⟩
    intro q hq
    simpa only [Bool.false_eq_true, ite_false] using
      (jordan_winding_constant hab.le x Γ hΓ hx hrange hclosed hp hq).trans hw

/-- The full rectifiable bound and circle characterization using one interior
winding witness, rather than a prescribed global orientation. -/
theorem jordan_isoperimetric_of_winding_witness (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Γ) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (p : Point) (hp : p ∈ jordanInterior Γ)
    (hw : |curveWinding hab.le (fun t : Icc a b => γ t) p| = 1) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht hst
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ hst)
  obtain ⟨orientation, ho⟩ := oriented_jordan_of_winding_witness hab
    (fun t : Icc a b => γ t) Γ hΓ hc.domRestrict hr hclosed hi p hp hw
  exact jordan_isoperimetric_rectifiable_interval γ hab hBV Γ orientation ho

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordanInterior_eq_component
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_winding_constant
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_of_winding_witness
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_of_winding_witness

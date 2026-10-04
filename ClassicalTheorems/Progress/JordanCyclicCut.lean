/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.SingleRayWinding

/-! Moving a simple loop's cut point, and removing the starting-point restriction
from the uniquely intersecting ray criterion. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A continuous simple closed loop recut at an interior parameter, with its
boundary image and winding preserved. The new parameter interval is `[0,2]`. -/
structure CyclicLoopCut {a b : ℝ} (hab : a < b) (x : Icc a b → Point)
    (s : Icc a b) where
  y : Icc (0 : ℝ) 2 → Point
  continuous : Continuous y
  range_eq : range y = range x
  closed : y ⟨0, by norm_num⟩ = y ⟨2, by norm_num⟩
  simple : InjOn y {t | (t : ℝ) < 2}
  start : y ⟨0, by norm_num⟩ = x s
  winding_eq : ∀ p, p ∉ range x →
    curveWinding (by norm_num : (0 : ℝ) ≤ 2) y p = curveWinding hab.le x p

/-- Construct a cyclic cut using imported concatenation, simplicity and winding
theorems, without copying their dependency proofs. -/
theorem nonempty_cyclic_loop_cut {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (hc : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) (s : Icc a b)
    (has : a < (s : ℝ)) (hsb : (s : ℝ) < b) : Nonempty (CyclicLoopCut hab x s) := by
  let A : Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Icc a b := ⟨b, hab.le, le_rfl⟩
  let φ : Icc (0 : ℝ) 1 → Icc a b := Icc.convexComb s B
  let ψ : Icc (0 : ℝ) 1 → Icc a b := Icc.convexComb A s
  have hφc : Continuous φ := Icc.continuous_convexComb s B
  have hψc : Continuous ψ := Icc.continuous_convexComb A s
  have hφ0 : φ ⟨0, by norm_num⟩ = s := by simp [φ]
  have hφ1 : φ ⟨1, by norm_num⟩ = B := by simp [φ]
  have hψ0 : ψ ⟨0, by norm_num⟩ = A := by simp [ψ]
  have hψ1 : ψ ⟨1, by norm_num⟩ = s := by simp [ψ]
  have hφm : StrictMono φ := by
    intro u v huv
    change (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * b <
      (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * b
    have huv' : (u : ℝ) < (v : ℝ) := huv
    nlinarith
  have hψm : StrictMono ψ := by
    intro u v huv
    change (1 - (u : ℝ)) * a + (u : ℝ) * (s : ℝ) <
      (1 - (v : ℝ)) * a + (v : ℝ) * (s : ℝ)
    have huv' : (u : ℝ) < (v : ℝ) := huv
    nlinarith
  have hjoin : (x ∘ φ) ⟨1, by norm_num⟩ = (x ∘ ψ) ⟨0, by norm_num⟩ := by
    simpa only [Function.comp_apply, hφ1, hψ0, A, B] using hclosed.symm
  let y := Function.concatUnitIntervals (x ∘ φ) (x ∘ ψ)
  have hyrange : range y = range x := by
    rw [Function.range_concatUnitIntervals _ _ hjoin]
    apply Subset.antisymm
    · rintro z (⟨u, rfl⟩ | ⟨u, rfl⟩) <;> exact mem_range_self _
    · rintro z ⟨t, rfl⟩
      rcases le_total s t with hst | hts
      · have hr : Icc s B ⊆ range φ := by
          simpa only [hφ0, hφ1] using intermediate_value_univ
            (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ hφc
        obtain ⟨u, hu⟩ := hr ⟨hst, t.property.2⟩
        exact Or.inl ⟨u, congrArg x hu⟩
      · have hr : Icc A s ⊆ range ψ := by
          simpa only [hψ0, hψ1] using intermediate_value_univ
            (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1) ⟨1, by norm_num⟩ hψc
        obtain ⟨u, hu⟩ := hr ⟨t.property.1, hts⟩
        exact Or.inr ⟨u, congrArg x hu⟩
  refine ⟨{
    y := y
    continuous := Function.continuous_concatUnitIntervals (hc.comp hφc) (hc.comp hψc) hjoin
    range_eq := hyrange
    closed := ?_
    simple := Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab.le
      hinj hclosed s has hsb φ ψ hφm hψm hφ0 hψ0 hψ1
    start := ?_
    winding_eq := ?_ }⟩
  · simp [y, φ, ψ]
  · simp [y, φ]
  · intro p hp
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab hc hp
    exact curveWinding_concat_of_cyclic_endpoints hab.le hθ hclosed s φ ψ
      hφc hψc hφ0 hφ1 hψ0 hψ1

/-- Unit winding from one uniquely intersecting ray through any boundary point.
The starting point of the supplied parametrization is unrestricted. -/
theorem winding_abs_one_of_unique_ray {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (p q : Point)
    (hc : Continuous x) (hrange : range x = Γ) (hp : p ∈ jordanInterior Γ) (hq : q ∈ Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b})
    (hunique : ∀ z ∈ Γ, radialDirection p z = radialDirection p q → z = q) :
    |curveWinding hab.le x p| = 1 := by
  obtain ⟨s, hs⟩ := hrange.symm ▸ hq
  by_cases has : a = (s : ℝ)
  · have he : s = (⟨a, le_rfl, hab.le⟩ : Icc a b) := Subtype.ext has.symm
    subst s
    subst q
    exact winding_abs_one_of_single_ray hab x Γ p hc hrange hp hclosed hinj hunique
  by_cases hsb : (s : ℝ) = b
  · have he : s = (⟨b, hab.le, le_rfl⟩ : Icc a b) := Subtype.ext hsb
    subst s
    have hqA : x ⟨a, le_rfl, hab.le⟩ = q := hclosed.trans hs
    apply winding_abs_one_of_single_ray hab x Γ p hc hrange hp hclosed hinj
    simpa only [hqA] using hunique
  obtain ⟨D⟩ := nonempty_cyclic_loop_cut hab x hc hclosed hinj s
    (lt_of_le_of_ne s.property.1 has) (lt_of_le_of_ne s.property.2 hsb)
  have hstart : D.y ⟨0, by norm_num⟩ = q := D.start.trans hs
  have hw := winding_abs_one_of_single_ray (by norm_num : (0 : ℝ) < 2)
    D.y Γ p D.continuous (D.range_eq.trans hrange) hp D.closed D.simple
    (by simpa only [hstart] using hunique)
  rw [D.winding_eq p (hrange ▸ hp.1)] at hw
  exact hw

/-- Some ray from `p` meets `Γ` at exactly one point. This condition depends only
on geometry and not on a boundary parametrization or its starting point. -/
def HasUniqueRadialRay (Γ : Set Point) (p : Point) : Prop :=
  ∃ q ∈ Γ, ∀ z ∈ Γ, radialDirection p z = radialDirection p q → z = q

/-- A uniquely intersecting ray through any boundary point determines global
Jordan orientation for the supplied parametrization. -/
theorem oriented_jordan_of_unique_ray {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hc : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) (p : Point) (hp : p ∈ jordanInterior Γ)
    (hunique : HasUniqueRadialRay Γ p) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x := by
  obtain ⟨q, hq, hu⟩ := hunique
  exact oriented_jordan_of_winding_witness hab x Γ hΓ hc hrange hclosed hinj p hp
    (winding_abs_one_of_unique_ray hab x Γ p q hc hrange hp hq hclosed hinj hu)

/-- Sharp isoperimetry and equality iff circle from the existence of any uniquely
intersecting radial ray. The original parametrization is left unrestricted. -/
theorem jordan_isoperimetric_unique_ray (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Γ) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (p : Point) (hp : p ∈ jordanInterior Γ)
    (hunique : HasUniqueRadialRay Γ p) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨q, hq, hu⟩ := hunique
  exact jordan_isoperimetric_of_winding_witness γ hab hBV Γ hΓ hc hrange hclosed hinj p hp
    (winding_abs_one_of_unique_ray hab (fun t : Icc a b => γ t) Γ p q
      hc.domRestrict hr hp hq hclosed hi hu)

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.nonempty_cyclic_loop_cut
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_abs_one_of_unique_ray
#check_upstream ClassicalTheorems.Progress.Isoperimetric.HasUniqueRadialRay
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_of_unique_ray
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_unique_ray

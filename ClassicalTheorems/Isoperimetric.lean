/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricRegular
import ClassicalTheorems.Progress.JordanCyclicCut
import ClassicalTheorems.Progress.SchoenfliesWinding

/-! The sharp classical isoperimetric bound for continuous rectifiable
Jordan curves, with geometric Lebesgue area and total-variation perimeter.
Equality is equivalent to a circle of positive radius, without any differentiability
or speed hypothesis, on any nondegenerate compact parameter interval. -/

namespace ClassicalTheorems
open MeasureTheory Set

theorem isoperimetric_inequality_smooth (D : Set ℂ) (γ : ℝ → ℂ) (L : ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hSpeed : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ = L) :
    4 * Real.pi * (volume D).toReal ≤
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
  obtain ⟨hLength, hBound⟩ :=
    Progress.Isoperimetric.jordan_isoperimetric_constant_speed D γ L
      hDomain hBounded hConnected hBoundary hCurve hClosed hSimple hPositive hSpeed
  simpa only [hLength] using hBound

/-- The smooth sharp bound, including the equality-only-for-circles conclusion. -/
theorem isoperimetric_theorem_smooth (D : Set ℂ) (γ : ℝ → ℂ) (L : ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hSpeed : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ = L) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 ∧
      (4 * Real.pi * (volume D).toReal = (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r) := by
  obtain ⟨hLength, hBound⟩ :=
    Progress.Isoperimetric.jordan_isoperimetric_constant_speed D γ L
      hDomain hBounded hConnected hBoundary hCurve hClosed hSimple hPositive hSpeed
  refine ⟨by simpa only [hLength] using hBound, ?_⟩
  intro heq
  rw [hLength] at heq
  exact Progress.Isoperimetric.jordan_isoperimetric_equality_circle D γ L
    hDomain hBounded hConnected hBoundary hCurve hClosed hSimple hPositive hSpeed heq

/-- The sharp bound for an arbitrary C¹ Jordan parametrization, including
parametrizations with stationary points. -/
theorem isoperimetric_inequality_c1 (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 :=
  Progress.Isoperimetric.jordan_isoperimetric_c1 D γ hDomain hBounded hConnected
    hBoundary hCurve hClosed hSimple hPositive

/-- The sharp bound and circle rigidity for a regular C¹ Jordan boundary.
The original parametrization has no constant-speed requirement. -/
theorem isoperimetric_theorem_regular (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hRegular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 ∧
      (4 * Real.pi * (volume D).toReal = (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_regular D γ hDomain hBounded hConnected
    hBoundary hCurve hClosed hSimple hRegular hPositive

/-- The sharp bound and circle rigidity for any positively oriented C¹ Jordan
parametrization. Stationary points are allowed. -/
theorem isoperimetric_theorem_c1 (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 ∧
      (4 * Real.pi * (volume D).toReal = (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_c1_complete D γ hDomain hBounded
    hConnected hBoundary hCurve hClosed hSimple hPositive

/-- The sharp bound for every continuous rectifiable Jordan parametrization.
Orientation is the topological winding condition of the Jordan-area dependency;
perimeter is total variation, without any differentiability or speed hypothesis. -/
theorem isoperimetric_inequality_rectifiable (γ : ℝ → MovingSofa.Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set MovingSofa.Point)
    (horiented : MovingSofa.IsOrientedJordanParametrization
      (by norm_num : (0 : ℝ) ≤ 1) Γ true (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 :=
  Progress.Isoperimetric.jordan_isoperimetric_rectifiable γ hBV Γ horiented

/-- The sharp classical theorem for a counterclockwise continuous rectifiable
Jordan curve, including the equality-only-for-circles conclusion. -/
theorem isoperimetric_theorem_rectifiable (γ : ℝ → MovingSofa.Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set MovingSofa.Point)
    (horiented : MovingSofa.IsOrientedJordanParametrization
      (by norm_num : (0 : ℝ) ≤ 1) Γ true (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 →
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  ⟨isoperimetric_inequality_rectifiable γ hBV Γ horiented,
    Progress.Isoperimetric.jordan_isoperimetric_equality_rectifiable γ hBV Γ horiented⟩

/-- The sharp classical bound and circle rigidity for either orientation of a
continuous rectifiable Jordan curve. Perimeter is total variation. -/
theorem isoperimetric_theorem_rectifiable_any_orientation (γ : ℝ → MovingSofa.Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set MovingSofa.Point)
    (orientation : Bool)
    (horiented : MovingSofa.IsOrientedJordanParametrization
      (by norm_num : (0 : ℝ) ≤ 1) Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 →
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_rectifiable_any_orientation
    γ hBV Γ orientation horiented

/-- Every circular boundary attains the sharp bound, for any simple rectifiable
Jordan parametrization in either orientation. -/
theorem isoperimetric_equality_of_circle (γ : ℝ → MovingSofa.Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set MovingSofa.Point)
    (orientation : Bool)
    (horiented : MovingSofa.IsOrientedJordanParametrization
      (by norm_num : (0 : ℝ) ≤ 1) Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t))
    (c : MovingSofa.Point) (r : ℝ) (hr : 0 < r) (hcircle : Γ = Metric.sphere c r) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 :=
  Progress.Isoperimetric.circle_isoperimetric_equality
    γ hBV Γ orientation horiented c r hr hcircle

/-- The full classical rectifiable isoperimetric theorem, with equality if and
only if the boundary is a circle of positive radius. Both orientations are allowed. -/
theorem isoperimetric_theorem_rectifiable_circle_iff (γ : ℝ → MovingSofa.Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set MovingSofa.Point)
    (orientation : Bool)
    (horiented : MovingSofa.IsOrientedJordanParametrization
      (by norm_num : (0 : ℝ) ≤ 1) Γ orientation (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_rectifiable_circle_iff
    γ hBV Γ orientation horiented

/-- The full classical theorem for either orientation and any nondegenerate
compact parameter interval, with equality exactly for circular boundaries. -/
theorem isoperimetric_theorem_rectifiable_interval (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (orientation : Bool)
    (horiented : MovingSofa.IsOrientedJordanParametrization hab.le Γ orientation
      (fun t : Icc a b => γ t)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_rectifiable_interval
    γ hab hBV Γ orientation horiented

/-- Exact geometric area and perimeter of a circular Jordan boundary, independent
of the compact parameter interval, speed and orientation. -/
theorem isoperimetric_circle_area_perimeter (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (orientation : Bool)
    (horiented : MovingSofa.IsOrientedJordanParametrization hab.le Γ orientation
      (fun t : Icc a b => γ t))
    (c : MovingSofa.Point) (r : ℝ) (hr : 0 < r) (hcircle : Γ = Metric.sphere c r) :
    (volume (MovingSofa.jordanInterior Γ)).toReal = Real.pi * r ^ 2 ∧
      (eVariationOn γ (Icc a b)).toReal = 2 * Real.pi * r :=
  Progress.Isoperimetric.circle_area_perimeter_interval
    γ hab hBV Γ orientation horiented c r hr hcircle

/-- The sharp theorem with explicit geometric hypotheses and a winding check
at just one interior point. Its sign and global orientation need not be supplied. -/
theorem isoperimetric_theorem_winding_witness (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (p : MovingSofa.Point) (hp : p ∈ MovingSofa.jordanInterior Γ)
    (hw : |MovingSofa.curveWinding hab.le (fun t : Icc a b => γ t) p| = 1) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_of_winding_witness
    γ hab hBV Γ hΓ hc hrange hclosed hinj p hp hw

/-- Circle formulas with no winding or orientation hypothesis. The given
continuous rectifiable parametrization is closed, simple, and covers the circle. -/
theorem circle_area_perimeter_unoriented (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (c : MovingSofa.Point) (r : ℝ) (hr : 0 < r)
    (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Metric.sphere c r)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    (volume (MovingSofa.jordanInterior (Metric.sphere c r))).toReal = Real.pi * r ^ 2 ∧
      (eVariationOn γ (Icc a b)).toReal = 2 * Real.pi * r :=
  Progress.Isoperimetric.simple_circle_area_perimeter
    γ hab hBV c r hr hc hrange hclosed hinj

/-- Convex Jordan interiors satisfy the full sharp theorem without a supplied
winding value or orientation, for any continuous rectifiable simple boundary. -/
theorem isoperimetric_theorem_convex (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hconvex : Convex ℝ (MovingSofa.jordanInterior Γ))
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_convex
    γ hab hBV Γ hΓ hconvex hc hrange hclosed hinj

/-- The sharp theorem from a geometric radial-uniqueness condition. This also
covers nonconvex boundaries whose radial projection is injective. -/
theorem isoperimetric_theorem_radial (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (p : MovingSofa.Point) (hp : p ∈ MovingSofa.jordanInterior Γ)
    (hrad : InjOn (Progress.Isoperimetric.radialDirection p) Γ) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_radial
    γ hab hBV Γ hΓ hc hrange hclosed hinj p hp hrad

/-- The sharp theorem for a Jordan boundary close to a radially unique reference
loop. Winding, convexity and radial injectivity of the actual boundary are unnecessary. -/
theorem isoperimetric_theorem_near_radial (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (y : C(Icc a b, MovingSofa.Point)) (p : MovingSofa.Point) (hp : p ∉ range y)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    (hyi : InjOn y {t | (t : ℝ) < b})
    (hyr : InjOn (Progress.Isoperimetric.radialDirection p) (range y))
    (hnear : ∀ t : Icc a b, ‖γ t - y t‖ < ‖y t - p‖) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_near_radial
    γ hab hBV Γ hΓ hc hrange hclosed hinj y p hp hyc hyi hyr hnear

/-- The full sharp theorem from a continuous deformation of closed loops avoiding
a basepoint, starting at a radial reference loop and ending at the given boundary.
Only the initial and final loops need be simple. -/
theorem isoperimetric_theorem_of_deformation (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hrange : γ '' Icc a b = Γ) (hinj : InjOn γ (Ico a b))
    (H : Icc (0 : ℝ) 1 → Icc a b → MovingSofa.Point) (p : MovingSofa.Point)
    (hH : Continuous (Function.uncurry H))
    (hclosed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩)
    (havoid : ∀ u, p ∉ range (H u))
    (hstart : InjOn (H ⟨0, by norm_num⟩) {t | (t : ℝ) < b})
    (hrad : InjOn (Progress.Isoperimetric.radialDirection p)
      (range (H ⟨0, by norm_num⟩)))
    (hend : H ⟨1, by norm_num⟩ = fun t : Icc a b => γ t) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_of_deformation
    γ hab hBV Γ hΓ hrange hinj H p hH hclosed havoid hstart hrad hend

/-- One uniquely intersecting ray from an interior point through the initial
boundary point gives sharp isoperimetry and equality precisely for circles. -/
theorem isoperimetric_theorem_single_ray (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (p : MovingSofa.Point) (hp : p ∈ MovingSofa.jordanInterior Γ)
    (hunique : ∀ z ∈ Γ, Progress.Isoperimetric.radialDirection p z =
      Progress.Isoperimetric.radialDirection p (γ a) → z = γ a) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_single_ray
    γ hab hBV Γ hΓ hc hrange hclosed hinj p hp hunique

/-- Any ray from an interior point meeting the boundary exactly once suffices for
sharp isoperimetry. Its intersection need not be the starting point of the curve. -/
theorem isoperimetric_theorem_unique_ray (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (p : MovingSofa.Point) (hp : p ∈ MovingSofa.jordanInterior Γ)
    (hunique : Progress.Isoperimetric.HasUniqueRadialRay Γ p) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_unique_ray
    γ hab hBV Γ hΓ hc hrange hclosed hinj p hp hunique

/-- Every continuous closed loop avoiding a point deforms, while avoiding that
point, to a unit circle traversed an integer number of times. -/
theorem closed_loop_integer_circle_deformation {a b : ℝ} (hab : a < b)
    (x : Icc a b → MovingSofa.Point) (p : MovingSofa.Point)
    (hx : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩) :
    Nonempty (Progress.Isoperimetric.IntegerCircleDeformation hab x p) :=
  Progress.Isoperimetric.nonempty_integer_circle_deformation hab x p hx hp hclosed

/-- A closed loop has zero winding precisely when it can be contracted to a
point through closed loops avoiding the basepoint. -/
theorem closed_loop_winding_zero_iff_contractible {a b : ℝ} (hab : a < b)
    (x : Icc a b → MovingSofa.Point) (p : MovingSofa.Point)
    (hx : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩) :
    MovingSofa.curveWinding hab.le x p = 0 ↔
      Nonempty (Progress.Isoperimetric.PuncturedLoopContraction hab x p) :=
  Progress.Isoperimetric.winding_zero_iff_contractible hab x p hx hp hclosed

/-- The sharp classical isoperimetric theorem for every rectifiable Jordan boundary.
Continuity and simplicity supply orientation; no winding witness is an input. -/
theorem isoperimetric_theorem_jordan (γ : ℝ → MovingSofa.Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) :=
  Progress.Isoperimetric.jordan_isoperimetric_unconditional
    γ hab hBV Γ hΓ hc hrange hclosed hinj

end ClassicalTheorems
#check_upstream ClassicalTheorems.isoperimetric_inequality_smooth
#check_upstream ClassicalTheorems.isoperimetric_theorem_smooth
#check_upstream ClassicalTheorems.isoperimetric_inequality_c1
#check_upstream ClassicalTheorems.isoperimetric_theorem_regular
#check_upstream ClassicalTheorems.isoperimetric_theorem_c1
#check_upstream ClassicalTheorems.isoperimetric_inequality_rectifiable
#check_upstream ClassicalTheorems.isoperimetric_theorem_rectifiable
#check_upstream ClassicalTheorems.isoperimetric_theorem_rectifiable_any_orientation
#check_upstream ClassicalTheorems.isoperimetric_equality_of_circle
#check_upstream ClassicalTheorems.isoperimetric_theorem_rectifiable_circle_iff
#check_upstream ClassicalTheorems.isoperimetric_theorem_rectifiable_interval
#check_upstream ClassicalTheorems.isoperimetric_circle_area_perimeter
#check_upstream ClassicalTheorems.isoperimetric_theorem_winding_witness
#check_upstream ClassicalTheorems.circle_area_perimeter_unoriented
#check_upstream ClassicalTheorems.isoperimetric_theorem_convex
#check_upstream ClassicalTheorems.isoperimetric_theorem_radial
#check_upstream ClassicalTheorems.isoperimetric_theorem_near_radial
#check_upstream ClassicalTheorems.isoperimetric_theorem_of_deformation
#check_upstream ClassicalTheorems.isoperimetric_theorem_single_ray
#check_upstream ClassicalTheorems.isoperimetric_theorem_unique_ray
#check_upstream ClassicalTheorems.closed_loop_integer_circle_deformation
#check_upstream ClassicalTheorems.closed_loop_winding_zero_iff_contractible

#check_upstream ClassicalTheorems.isoperimetric_theorem_jordan

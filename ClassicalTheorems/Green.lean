/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenPolygon

/-! Green's theorem for a positively oriented regular C¹ simple closed boundary.
The proof uses the Jordan signed-area identity, compact-support extensions and small shears. -/

namespace ClassicalTheorems
open MeasureTheory

theorem greens_theorem (D U : Set ℂ) (γ : ℝ → ℂ) (P Q : ℂ → ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Set.Icc 0 1)
    (hOpen : IsOpen U) (hNeighborhood : closure D ⊆ U)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : Set.InjOn γ (Set.Ico 0 1))
    (hRegular : ∀ t ∈ Set.Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    (∫ t in (0 : ℝ)..1, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) =
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I :=
  ClassicalTheorems.Progress.Green.greens_theorem D U γ P Q hDomain hBounded hConnected
    hBoundary hOpen hNeighborhood hCurve hClosed hSimple hRegular hPositive hP hQ

/-- Positive Green identity allowing stationary points on the boundary. -/
alias greens_theorem_without_regularity :=
  ClassicalTheorems.Progress.Green.greens_theorem_without_regularity

/-- The boundary constructs one sign that works for every coefficient pair. -/
alias greens_theorem_either_orientation :=
  ClassicalTheorems.Progress.Green.greens_theorem_either_orientation

/-- A positive winding check at one domain point suffices. -/
alias greens_theorem_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_of_positive_winding_at

/-- Green identity in absolute value, with no orientation input. -/
alias greens_theorem_abs := ClassicalTheorems.Progress.Green.greens_theorem_abs

/-- Automatic signed Green on any nondegenerate compact parameter interval. -/
alias greens_theorem_interval := ClassicalTheorems.Progress.Green.greens_theorem_interval

/-- One positive winding check on any nondegenerate compact parameter interval. -/
alias greens_theorem_interval_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_interval_of_positive_winding_at

/-- Orientation-independent Green on any nondegenerate compact parameter interval. -/
alias greens_theorem_interval_abs := ClassicalTheorems.Progress.Green.greens_theorem_interval_abs

/-- Signed Green for a curve C¹ only on a neighborhood of its parameter interval. -/
alias greens_theorem_local_curve := ClassicalTheorems.Progress.Green.greens_theorem_local_curve

/-- One positive winding check for a curve C¹ only near its parameter interval. -/
alias greens_theorem_local_curve_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_local_curve_of_positive_winding_at

/-- Orientation-independent Green for a curve C¹ only near its parameter interval. -/
alias greens_theorem_local_curve_abs :=
  ClassicalTheorems.Progress.Green.greens_theorem_local_curve_abs

/-- Signed Green after a locally C¹ clock, allowing pauses and retraced arcs. -/
alias greens_theorem_reparametrized := ClassicalTheorems.Progress.Green.greens_theorem_reparametrized

/-- One positive winding check after a locally C¹ clock. -/
alias greens_theorem_reparametrized_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_reparametrized_of_positive_winding_at

/-- Orientation-independent Green after a locally C¹ clock. -/
alias greens_theorem_reparametrized_abs :=
  ClassicalTheorems.Progress.Green.greens_theorem_reparametrized_abs

/-- Signed Green for a finite simple closed C¹ chain with arbitrary corners. -/
alias greens_theorem_piecewise := ClassicalTheorems.Progress.Green.greens_theorem_piecewise

/-- One positive winding check gives the usual finite-piece Green formula. -/
alias greens_theorem_piecewise_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_piecewise_of_positive_winding_at

/-- Orientation-independent Green for a finite C¹ chain with arbitrary corners. -/
alias greens_theorem_piecewise_abs := ClassicalTheorems.Progress.Green.greens_theorem_piecewise_abs

/-- Signed Green with each finite piece C¹ only near its own unit interval. -/
alias greens_theorem_piecewise_local :=
  ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local

/-- One positive winding check for a finite chain of locally C¹ pieces. -/
alias greens_theorem_piecewise_local_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local_of_positive_winding_at

/-- Orientation-independent Green for finite pieces C¹ only near their intervals. -/
alias greens_theorem_piecewise_local_abs :=
  ClassicalTheorems.Progress.Green.greens_theorem_piecewise_local_abs

export ClassicalTheorems.Progress.Green
  (polygonOfVertices polygonVertex polygonEdge polygonInterior polygonLineIntegral)

/-- Signed Green from a certified vertex polygon; its domain geometry is inferred. -/
alias greens_theorem_polygon := ClassicalTheorems.Progress.Green.greens_theorem_polygon

/-- One positive winding check fixes the sign of the vertex-polygon Green formula. -/
alias greens_theorem_polygon_of_positive_winding_at :=
  ClassicalTheorems.Progress.Green.greens_theorem_polygon_of_positive_winding_at

/-- Orientation-independent Green from a certified vertex polygon. -/
alias greens_theorem_polygon_abs := ClassicalTheorems.Progress.Green.greens_theorem_polygon_abs

/-- The existing noncollinear-triangle constructor discharges all polygon geometry. -/
alias greens_theorem_triangle_abs := ClassicalTheorems.Progress.Green.greens_theorem_triangle_abs

end ClassicalTheorems

#check_upstream ClassicalTheorems.greens_theorem

#check_upstream ClassicalTheorems.greens_theorem_without_regularity
#check_upstream ClassicalTheorems.greens_theorem_either_orientation
#check_upstream ClassicalTheorems.greens_theorem_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_abs

#check_upstream ClassicalTheorems.greens_theorem_interval
#check_upstream ClassicalTheorems.greens_theorem_interval_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_interval_abs

#check_upstream ClassicalTheorems.greens_theorem_local_curve

#check_upstream ClassicalTheorems.greens_theorem_local_curve_of_positive_winding_at

#check_upstream ClassicalTheorems.greens_theorem_local_curve_abs

#check_upstream ClassicalTheorems.greens_theorem_reparametrized
#check_upstream ClassicalTheorems.greens_theorem_reparametrized_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_reparametrized_abs

#check_upstream ClassicalTheorems.greens_theorem_piecewise
#check_upstream ClassicalTheorems.greens_theorem_piecewise_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_piecewise_abs

#check_upstream ClassicalTheorems.greens_theorem_piecewise_local
#check_upstream ClassicalTheorems.greens_theorem_piecewise_local_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_piecewise_local_abs

#check_upstream ClassicalTheorems.polygonOfVertices
#check_upstream ClassicalTheorems.polygonVertex
#check_upstream ClassicalTheorems.polygonEdge
#check_upstream ClassicalTheorems.polygonInterior
#check_upstream ClassicalTheorems.polygonLineIntegral
#check_upstream ClassicalTheorems.greens_theorem_polygon
#check_upstream ClassicalTheorems.greens_theorem_polygon_of_positive_winding_at
#check_upstream ClassicalTheorems.greens_theorem_polygon_abs
#check_upstream ClassicalTheorems.greens_theorem_triangle_abs

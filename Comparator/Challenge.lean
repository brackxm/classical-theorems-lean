/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib
import ClassicalTheorems.Statements.Arithmetic
import ClassicalTheorems.Statements.Tarski
import ClassicalTheorems.Progress.PolytopeFaces
import MovingSofa.Curve.Jordan.Orientation
import Schoenflies.CrosscutCells
import HOLLightPort.Pascal
import HOLLightPort.Desargues

/-!
# Independently stated contracts for the ten indexed propositions

Review these statements and the definitions they mention when changing the theorem index.
They deliberately use `sorry`: `lake comparator` compares them with the actual library types
and checks the solution proofs, including their transitive axioms and kernel replay.
This file is outside the default library and is never imported by production proofs.

The statements are maintained by hand. `scripts/check_comparator.py --write` generates only
the solution wrappers and configuration; it must not regenerate these statements from proofs.
The comparator checks formal agreement, not whether our definitions express the intended
mathematics. In particular, review the arithmetic language, neutral-plane axioms, face counts,
Jordan interior, and homogeneous-coordinate definitions alongside these statements.
-/

open Set MeasureTheory
open ClassicalTheorems.Statements.Arithmetic ClassicalTheorems.Statements.Geometry
open LeanEval.Geometry.PlatonicClassification

/-- Every satisfiable recursively enumerable extension of Robinson Q has an independent sentence. -/
theorem Comparator.ClassicalTheorems.godel_incompleteness (theory : language.Theory)
    (hArithmetic : robinson ⊆ theory) (hEnumerable : RecursivelyEnumerable theory)
    (hConsistent : theory.IsSatisfiable) :
    ∃ φ : language.Sentence,
      (theory ∪ {φ}).IsSatisfiable ∧ (theory ∪ {φ.not}).IsSatisfiable := sorry

/-- Neutral Tarski planes with continuity can satisfy or refute the parallel postulate. -/
theorem Comparator.ClassicalTheorems.parallel_postulate_independence :
    ∃ euclidean hyperbolic : NeutralPlane,
      euclidean.ParallelPostulate ∧ ¬hyperbolic.ParallelPostulate := sorry

/-- Euler's formula counts actual exposed faces of a full-dimensional convex polytope. -/
theorem Comparator.ClassicalTheorems.euler_polyhedron
    (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (ClassicalTheorems.Progress.Euler.faceCount P 0 : ℤ) -
      (ClassicalTheorems.Progress.Euler.faceCount P 1 : ℤ) +
      (ClassicalTheorems.Progress.Euler.faceCount P 2 : ℤ) = 2 := sorry

/-- Green's curl formula with a positively oriented regular C¹ Jordan boundary. -/
theorem Comparator.ClassicalTheorems.greens_theorem
    (D U : Set ℂ) (γ : ℝ → ℂ) (P Q : ℂ → ℝ)
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
      ∫ z in D, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := sorry

/-- The sharp rectifiable Jordan inequality, with equality exactly for circles. -/
theorem Comparator.ClassicalTheorems.isoperimetric_theorem_jordan
    (γ : ℝ → MovingSofa.Point) {a b : ℝ} (hab : a < b)
    (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set MovingSofa.Point) (hΓ : MovingSofa.IsJordanCurve Γ)
    (hc : ContinuousOn γ (Icc a b)) (hrange : γ '' Icc a b = Γ)
    (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b)) :
    4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (MovingSofa.jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : MovingSofa.Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := sorry

/-- Heron's formula uses the Lebesgue area enclosed by three noncollinear sides. -/
theorem Comparator.ClassicalTheorems.heron_area (a b c : Schoenflies.Plane)
    (h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0) :
    let x := dist a b
    let y := dist b c
    let z := dist c a
    let s := (x + y + z) / 2
    (volume (Schoenflies.inside (segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a))).toReal =
      Real.sqrt (s * (s - x) * (s - y) * (s - z)) := sorry

/-- Six homogeneous points on a nonzero quadratic conic have collinear opposite intersections. -/
theorem Comparator.HOLLightPort.Pascal.pascal.{u_1} {K : Type u_1} [Field K]
    (p : Fin 6 → Fin 3 → K) (coeff : Fin 6 → K)
    (hc : coeff ≠ 0) (hp : ∀ i, dotProduct (HOLLightPort.Pascal.veronese (p i)) coeff = 0) :
    (HOLLightPort.Pascal.intersections p).det = 0 := sorry

/-- Pascal's nonsingular symmetric-matrix formulation in characteristic zero. -/
theorem Comparator.HOLLightPort.Pascal.pascals_hexagon.{u_1} {K : Type u_1} [Field K]
    [CharZero K] (A : Matrix (Fin 3) (Fin 3) K) (p : Fin 6 → Fin 3 → K)
    (hs : A.transpose = A) (ha : A.det ≠ 0)
    (hp : ∀ i, dotProduct (p i) (A.mulVec (p i)) = 0) :
    (HOLLightPort.Pascal.intersections p).det = 0 := sorry

/-- Desargues: concurrency of corresponding joins implies collinear side intersections. -/
theorem Comparator.HOLLightPort.Desargues.desargues.{u_1} {K : Type u_1} [Field K]
    (a b : Matrix (Fin 3) (Fin 3) K) (o : Fin 3 → K)
    (ho : o ≠ 0) (hp : ∀ i, dotProduct (HOLLightPort.Desargues.cross (a i) (b i)) o = 0) :
    ∃ line ≠ (0 : Fin 3 → K), ∀ i, dotProduct (HOLLightPort.Desargues.meets a b i) line = 0 := sorry

/-- Desargues's converse for noncollinear triangles over any field. -/
theorem Comparator.HOLLightPort.Desargues.desargues_converse.{u_1}
    {K : Type u_1} [Field K] (a b : Matrix (Fin 3) (Fin 3) K)
    (ha : a.det ≠ 0) (hb : b.det ≠ 0) (line : Fin 3 → K) (hl : line ≠ 0)
    (hp : ∀ i, dotProduct (HOLLightPort.Desargues.meets a b i) line = 0) :
    ∃ o ≠ (0 : Fin 3 → K), ∀ i,
      dotProduct (HOLLightPort.Desargues.cross (a i) (b i)) o = 0 := sorry

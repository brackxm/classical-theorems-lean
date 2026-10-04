/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.HeronAlgebra
import ClassicalTheorems.Progress.GreenPolygon
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Heron's formula for the actual Lebesgue area enclosed by a noncollinear
triangle. Green's theorem identifies this area with the coordinate determinant;
the remaining identity uses the three Euclidean side lengths. -/

noncomputable section
open Set MeasureTheory
open ClassicalTheorems.Progress.Green
namespace ClassicalTheorems

private theorem edge_area_integral (a b : ℂ) :
    (∫ t in (0 : ℝ)..1, (AffineMap.lineMap a b t).re * (b - a).im) =
      (a.re + b.re) * (b.im - a.im) / 2 := by
  have he : (fun t : ℝ => (AffineMap.lineMap a b t).re * (b - a).im) =
      fun t => (t * (b.re - a.re) + a.re) * (b.im - a.im) := by
    funext t
    simp [AffineMap.lineMap_apply]
  rw [he, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_mul_const, integral_id, intervalIntegral.integral_const]
  ring

/-- The Lebesgue area of the bounded region enclosed by a noncollinear triangle. -/
private theorem triangle_complex_area_eq_det (a b c : Schoenflies.Plane)
    (h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0) :
    (volume (polygonInterior (Schoenflies.triangle h).toPre)).toReal =
      |Schoenflies.Plane.det (b - a) (c - a)| / 2 := by
  have hg := greens_theorem_triangle_abs a b c h univ isOpen_univ
    (subset_univ _) (fun _ => 0) Complex.re (by fun_prop) Complex.reCLM.contDiff.contDiffOn
  have hd : (fun z : ℂ => fderiv ℝ Complex.re z (1 : ℂ) -
      fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z Complex.I) = fun _ => (1 : ℝ) := by
    funext z
    change (fderiv ℝ (Complex.reCLM : ℂ → ℝ) z) 1 -
      (fderiv ℝ (fun _ : ℂ => (0 : ℝ)) z) Complex.I = 1
    simp [ContinuousLinearMap.fderiv]
  rw [hd, integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_one,
    abs_of_nonneg measureReal_nonneg] at hg
  have hb : polygonLineIntegral (Schoenflies.triangle h).toPre (fun _ => 0) Complex.re =
      Schoenflies.Plane.det (b - a) (c - a) / 2 := by
    simp only [polygonLineIntegral, zero_mul, zero_add, polygonEdge]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_zero, zero_add]
    rw [edge_area_integral, edge_area_integral, edge_area_integral]
    norm_num [polygonVertex, Schoenflies.triangle, Schoenflies.ClosedPolygon.toPre,
      Complex.orthonormalBasisOneI_repr_symm_apply, Schoenflies.Plane.det]
    ring
  rw [hb, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hg
  exact hg.symm

/-- The certified triangle's boundary is exactly its three Euclidean sides. -/
theorem triangle_carrier (a b c : Schoenflies.Plane)
    (h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0) :
    (Schoenflies.triangle h).toPre.carrier =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a := by
  ext z
  simp only [Schoenflies.PrePolygon.carrier, mem_iUnion, Schoenflies.PrePolygon.edge]
  change (∃ i : ZMod 3, z ∈ segment ℝ ((Schoenflies.triangle h).vertex i)
    ((Schoenflies.triangle h).vertex (i+1))) ↔ _
  have hcases : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  constructor
  · rintro ⟨i, hi⟩
    rcases hcases i with rfl | rfl | rfl
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi
  · rintro ((hab | hbc) | hca)
    · exact ⟨0, hab⟩
    · exact ⟨1, hbc⟩
    · exact ⟨2, hca⟩

/-- Determinant formula for the Lebesgue area of a triangle in the Euclidean plane. -/
theorem triangle_area_eq_det (a b c : Schoenflies.Plane)
    (h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0) :
    (volume (Schoenflies.inside (Schoenflies.triangle h).toPre.carrier)).toReal =
      |Schoenflies.Plane.det (b - a) (c - a)| / 2 := by
  rw [← polygonInterior_volume (Schoenflies.triangle h).toPre]
  exact triangle_complex_area_eq_det a b c h

/-- **Heron's formula:** the Lebesgue area enclosed by three noncollinear
Euclidean vertices is the square root of the semiperimeter product. -/
theorem heron_area (a b c : Schoenflies.Plane)
    (h : Schoenflies.Plane.det (b - a) (c - a) ≠ 0) :
    let x := dist a b
    let y := dist b c
    let z := dist c a
    let s := (x + y + z) / 2
    (volume (Schoenflies.inside (segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a))).toReal =
      Real.sqrt (s * (s - x) * (s - y) * (s - z)) := by
  rw [← triangle_carrier a b c h]
  exact (triangle_area_eq_det a b c h).trans (heron_det a b c).symm

#check_upstream ClassicalTheorems.triangle_carrier
#check_upstream ClassicalTheorems.triangle_area_eq_det
#check_upstream ClassicalTheorems.heron_det
#check_upstream ClassicalTheorems.heron_area
end ClassicalTheorems

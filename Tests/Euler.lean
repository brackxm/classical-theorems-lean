/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Euler
import Mathlib.Tactic.NormNum

/-!
# Geometric face counts for a translated, nonregular tetrahedron

The vertices are (2, -1, 3), (5, -1, 3), (2, 3, 3), and (2, -1, 8).
We construct their actual convex hull as a valid full-dimensional polytope,
establish a triangular exposed facet, and count its geometric faces before
applying the public Euler theorem. No Euler equation or face counts are
assumed in constructing the polytope.
-/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ClassicalTheorems.Progress.Euler

namespace ClassicalTheoremsTest.Euler

private abbrev points : Fin 4 → E 3 :=
  ![!₂[2, -1, 3], !₂[5, -1, 3], !₂[2, 3, 3], !₂[2, -1, 8]]

private theorem independent_points : AffineIndependent ℝ points := by
  apply (affineIndependent_iff_of_fintype ℝ points).mpr
  intro w hsum hw i
  rw [Finset.weightedVSub_eq_linear_combination Finset.univ hsum] at hw
  simp only [Fin.sum_univ_succ] at hw
  have hx := congrArg (fun v : E 3 => v 0) hw
  have hy := congrArg (fun v : E 3 => v 1) hw
  have hz := congrArg (fun v : E 3 => v 2) hw
  norm_num [points, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hx hy hz
  norm_num [Fin.sum_univ_succ] at hsum
  fin_cases i
  · change w 0 = 0
    linarith
  · change w 1 = 0
    linarith
  · change w 2 = 0
    linarith
  · change w 3 = 0
    linarith

private def basis : AffineBasis (Fin 4) ℝ (E 3) :=
  ⟨points, independent_points,
    independent_points.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp [E])⟩

private def vertices : Finset (E 3) := Finset.univ.image points

private theorem vertices_range : (vertices : Set (E 3)) = range basis := by
  change (↑(Finset.univ.image points) : Set (E 3)) = range points
  simp only [Finset.coe_image, Finset.coe_univ, image_univ]

-- Expose each vertex using its barycentric coordinate. This verifies the
-- polytope's extreme-point requirement without presupposing a valid polytope.
private theorem exposed_vertex (i : Fin 4) :
    IsExposed ℝ (convexHull ℝ (vertices : Set (E 3))) {basis i} := by
  let f := basis.coord i
  let l : E 3 →L[ℝ] ℝ := f.linear.toContinuousLinearMap
  have hl (x : E 3) : l x = f x - f 0 := by
    change f.linear x = f x - f 0
    exact congrFun f.decomp' x
  have hmem : basis i ∈ convexHull ℝ (vertices : Set (E 3)) :=
    subset_convexHull ℝ _ (vertices_range ▸ mem_range_self i)
  have hbound : ∀ x ∈ convexHull ℝ (vertices : Set (E 3)), l x ≤ l (basis i) := by
    apply convexHull_min _ (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) _)
    rintro x hx
    rw [vertices_range] at hx
    obtain ⟨j, rfl⟩ := hx
    change l (basis j) ≤ l (basis i)
    rw [hl, hl]
    simp only [f, AffineBasis.coord_apply]
    split_ifs <;> linarith
  intro _
  refine ⟨l, ?_⟩
  ext x
  constructor
  · rintro rfl
    exact ⟨hmem, hbound⟩
  · rintro ⟨hx, hmax⟩
    have hvalue : l x = l (basis i) := le_antisymm (hbound x hx) (hmax _ hmem)
    have harg := PlatoniciL3.faccia_argmax vertices l hx hmax
    have hsubset : {v ∈ (vertices : Set (E 3)) | l v = l x} ⊆ {basis i} := by
      rintro v ⟨hv, he⟩
      rw [vertices_range] at hv
      obtain ⟨j, rfl⟩ := hv
      by_cases hij : i = j
      · subst j
        exact mem_singleton _
      · have heq := he.trans hvalue
        rw [hl, hl] at heq
        simp only [f, AffineBasis.coord_apply, hij, ite_false, ite_true] at heq
        linarith
    have hxsingle : x ∈ convexHull ℝ ({basis i} : Set (E 3)) :=
      convexHull_mono hsubset harg
    simpa using hxsingle

private def tetrahedron : ConvexPolytope 3 where
  vertices := vertices
  vertices_nonempty := ⟨points 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩
  vertices_eq_extremePoints := by
    apply Subset.antisymm
    · intro x hx
      rw [vertices_range] at hx
      obtain ⟨i, rfl⟩ := hx
      exact (exposed_vertex i).isExtreme.mem_extremePoints
    · exact extremePoints_convexHull_subset

/-- The concrete hull spans all of three-dimensional Euclidean space. -/
theorem solid_tetrahedron : tetrahedron.IsFullDim := by
  change Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (vertices : Set (E 3)))) = 3
  rw [← direction_affineSpan, affineSpan_convexHull, vertices_range, basis.tot,
    AffineSubspace.direction_top]
  simp [E]

/-- The listed generators are exactly the four geometric vertices. -/
theorem four_vertices : tetrahedron.vertices.card = 4 := by
  change (Finset.univ.image points).card = 4
  rw [Finset.card_image_of_injective _ independent_points.injective]
  simp

private def base : Set (E 3) :=
  convexHull ℝ (basis '' (({0, 1, 2} : Finset (Fin 4)) : Set (Fin 4)))

/-- The first three vertices form a genuine exposed triangular facet. -/
theorem triangular_base : tetrahedron.IsFace base ∧ ConvexPolytope.faceDim base = 2 := by
  constructor
  · exact basis_hull_isFace tetrahedron basis vertices_range {0, 1, 2} (by decide)
  · exact basis_hull_faceDim basis {0, 1, 2} 2 (by decide)

/-- Count actual faces: 4 vertices, 6 edges, 4 facets, one body, and no 4-faces. -/
theorem geometric_face_counts :
    faceCount tetrahedron 0 = 4 ∧ faceCount tetrahedron 1 = 6 ∧
    faceCount tetrahedron 2 = 4 ∧ faceCount tetrahedron 3 = 1 ∧
    faceCount tetrahedron 4 = 0 := by
  have h0 := basis_faceCount tetrahedron basis vertices_range 0
  have h1 := basis_faceCount tetrahedron basis vertices_range 1
  have h2 := basis_faceCount tetrahedron basis vertices_range 2
  have h3 := basis_faceCount tetrahedron basis vertices_range 3
  have h4 := basis_faceCount tetrahedron basis vertices_range 4
  norm_num at h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2, h3, h4⟩

/-- Apply the indexed theorem to this independently constructed solid polytope. -/
theorem euler_characteristic :
    (faceCount tetrahedron 0 : ℤ) - (faceCount tetrahedron 1 : ℤ) +
      (faceCount tetrahedron 2 : ℤ) = 2 :=
  ClassicalTheorems.euler_polyhedron tetrahedron solid_tetrahedron

#check_upstream solid_tetrahedron
#check_upstream four_vertices
#check_upstream triangular_base
#check_upstream geometric_face_counts
#check_upstream euler_characteristic

end ClassicalTheoremsTest.Euler

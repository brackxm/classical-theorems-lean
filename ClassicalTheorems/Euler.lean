/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.SimplexEuler
import ClassicalTheorems.Progress.PyramidEuler

/-! Euler's formula for every solid convex polyhedron. Vertices, edges
and facets are counted as actual exposed faces of a finite convex hull. -/

namespace ClassicalTheorems
open LeanEval.Geometry.PlatonicClassification

/-- Euler's formula for every solid convex polyhedron in Euclidean three-space,
counting actual exposed faces of its convex hull. -/
theorem euler_polyhedron (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) = 2 :=
  Progress.Euler.polyhedron_euler P hfull

/-- Every geometric edge cycle is the boundary of a sum of actual facets. -/
theorem polyhedron_cycle_filling (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∀ z : Progress.Euler.PolytopeFace P 1 → ZMod 2,
      (Progress.Euler.vertexIncidence P).transpose.mulVec z = 0 →
      ∃ c : Progress.Euler.PolytopeFace P 2 → ZMod 2,
        (Progress.Euler.facetIncidence P).mulVec c = z :=
  Progress.Euler.polyhedron_cycle_filling P hfull

/-- The classical edge bound follows from geometric Euler and facet incidences. -/
theorem polyhedron_edges_le_three_vertices_sub_six (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) :
    Progress.Euler.faceCount P 1 ≤ 3 * Progress.Euler.faceCount P 0 - 6 :=
  Progress.Euler.polyhedron_edges_le_three_vertices_sub_six P hfull

/-- Every solid tetrahedron satisfies Euler's polyhedron formula, with no
regularity, Euler-characteristic, or abstract embedding assumption. -/
theorem euler_polyhedron_tetrahedron (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (hvertices : P.vertices.card = 4) :
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) = 2 :=
  Progress.Euler.four_vertex_polytope_euler P hfull hvertices

/-- Every convex pyramid with an arbitrary polygonal base satisfies Euler's
formula. The base and apex hypotheses imply full dimension; all counted
vertices, edges, and facets are genuine exposed faces of the convex hull. -/
theorem euler_polyhedron_pyramid (P : ConvexPolytope 3) (B : Set (E 3)) (a : E 3)
    (hB : P.IsFace B) (hdB : ConvexPolytope.faceDim B = 2)
    (ha : a ∈ P.vertices) (haB : a ∉ B)
    (hvertices : ∀ v ∈ P.vertices, v = a ∨ v ∈ B) :
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) = 2 :=
  Progress.Euler.pyramid_euler P ⟨hB, hdB, ha, haB, hvertices⟩

/-- Every convex polygon has equally many genuine geometric vertices and
edges, independent of its number of vertices or embedding dimension. -/
theorem euler_convex_polygon {n : ℕ} (P : ConvexPolytope n) (hdim : P.dim = 2) :
    Progress.Euler.faceCount P 1 = Progress.Euler.faceCount P 0 ∧
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) = 1 :=
  ⟨Progress.Euler.polygon_faceCount_one P hdim, Progress.Euler.polygon_euler P hdim⟩

/-- The general geometric edge-facet incidence count and its facet bound.
These hold for all solid convex polyhedra, without an Euler hypothesis. -/
theorem polyhedron_geometric_incidence (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (∑ F ∈ Progress.Euler.faceFinset P 2, (Progress.Euler.faceVertices P F).card) =
      2 * Progress.Euler.faceCount P 1 ∧
    3 * Progress.Euler.faceCount P 2 ≤ 2 * Progress.Euler.faceCount P 1 :=
  ⟨Progress.Euler.polyhedron_vertex_facet_handshake P hfull,
    Progress.Euler.polyhedron_three_facets_le_two_edges P hfull⟩

/-- Every solid convex polyhedron satisfies the global geometric upper bound
on Euler's expression. No planarity or Euler-characteristic hypothesis is used. -/
theorem euler_polyhedron_upper_bound (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) ≤ 2 :=
  Progress.Euler.polyhedron_euler_le_two P hfull

/-- The general Euler equality is equivalent to filling every
geometric edge cycle with a sum of actual facet boundaries over 𝔽₂. -/
theorem euler_polyhedron_cycle_filling_iff (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (Progress.Euler.faceCount P 0 : ℤ) - (Progress.Euler.faceCount P 1 : ℤ) +
      (Progress.Euler.faceCount P 2 : ℤ) = 2 ↔
    ∀ z : Progress.Euler.PolytopeFace P 1 → ZMod 2,
      (Progress.Euler.vertexIncidence P).transpose.mulVec z = 0 →
      ∃ c : Progress.Euler.PolytopeFace P 2 → ZMod 2,
        (Progress.Euler.facetIncidence P).mulVec c = z :=
  Progress.Euler.polyhedron_euler_eq_two_iff_cycle_filling P hfull

end ClassicalTheorems
#check_upstream ClassicalTheorems.euler_polyhedron
#check_upstream ClassicalTheorems.polyhedron_cycle_filling
#check_upstream ClassicalTheorems.polyhedron_edges_le_three_vertices_sub_six
#check_upstream ClassicalTheorems.euler_polyhedron_tetrahedron
#check_upstream ClassicalTheorems.euler_convex_polygon
#check_upstream ClassicalTheorems.polyhedron_geometric_incidence
#check_upstream ClassicalTheorems.euler_polyhedron_pyramid
#check_upstream ClassicalTheorems.euler_polyhedron_upper_bound
#check_upstream ClassicalTheorems.euler_polyhedron_cycle_filling_iff

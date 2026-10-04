/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.CycleElimination

/-! Euler's formula for every solid convex polyhedron.
A generic linear height and descending geometric vertex figures fill every
edge cycle by actual facet boundaries. Finite induction eliminates vertices
in decreasing height. The already proved incidence rank criterion then gives
V - E + F = 2. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- Vertices below a given real height threshold. -/
def verticesBelow (P : ConvexPolytope 3) (h : E 3 →L[ℝ] ℝ) (t : ℝ) : Finset (E 3) :=
  P.vertices.filter (fun x => h x < t)

/-- Every nonzero edge coefficient has both endpoints below the threshold. -/
def SupportedBelow (P : ConvexPolytope 3) (h : E 3 →L[ℝ] ℝ) (t : ℝ)
    (z : PolytopeFace P 1 → ZMod 2) : Prop :=
  ∀ q, z q ≠ 0 → ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val < t

/-- A descending local filling at every vertex fills every geometric edge
cycle globally, by finite induction on the number of allowed vertices. -/
theorem cycle_filling_of_local (P : ConvexPolytope 3) (h : E 3 →L[ℝ] ℝ)
    (hinj : Set.InjOn h (P.vertices : Set (E 3)))
    (hfill : ∀ (v : PolytopeVertex P) (z : DescendingEdge P v h → ZMod 2),
      (∑ e, z e) = 0 → ∃ c : DescendingFacet P v h → ZMod 2,
        (descendingIncidence P v h).transpose.mulVec c = z) :
    ∀ z : PolytopeFace P 1 → ZMod 2, (vertexIncidence P).transpose.mulVec z = 0 →
      ∃ c : PolytopeFace P 2 → ZMod 2, (facetIncidence P).mulVec c = z := by
  have main : ∀ n : ℕ, ∀ t : ℝ, (verticesBelow P h t).card = n →
      ∀ z : PolytopeFace P 1 → ZMod 2,
        (vertexIncidence P).transpose.mulVec z = 0 → SupportedBelow P h t z →
        ∃ c : PolytopeFace P 2 → ZMod 2, (facetIncidence P).mulVec c = z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t hcard z hz hs
      by_cases hne : (verticesBelow P h t).Nonempty
      · obtain ⟨a, ha, hmax⟩ := (verticesBelow P h t).exists_max_image h hne
        have ha' : a ∈ P.vertices ∧ h a < t := Finset.mem_filter.mp ha
        let v : PolytopeVertex P := ⟨a, ha'.1⟩
        have htop : ∀ q, z q ≠ 0 → ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val ≤ h v.val := by
          intro q hq x hxq
          exact hmax x.val (Finset.mem_filter.mpr ⟨x.property, hs q hq x hxq⟩)
        obtain ⟨g, hgCycle, hgBelow⟩ := eliminate_highest_cycle_vertex P v h hinj (hfill v) z hz htop
        have hsub : verticesBelow P h (h v.val) ⊆ verticesBelow P h t := by
          intro x hx
          obtain ⟨hxV, hxlt⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hxV, lt_trans hxlt ha'.2⟩
        have hvnot : v.val ∉ verticesBelow P h (h v.val) := by simp [verticesBelow]
        have hstrict : verticesBelow P h (h v.val) ⊂ verticesBelow P h t := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
          intro heq
          apply hvnot
          rw [heq]
          exact ha
        have hlt : (verticesBelow P h (h v.val)).card < n := by
          rw [← hcard]
          exact Finset.card_lt_card hstrict
        obtain ⟨c, hc⟩ := ih (verticesBelow P h (h v.val)).card hlt (h v.val) rfl
          (z + (facetIncidence P).mulVec g) hgCycle hgBelow
        refine ⟨c + g, ?_⟩
        rw [Matrix.mulVec_add, hc]
        ext q
        change (z q + (facetIncidence P).mulVec g q) + (facetIncidence P).mulVec g q = z q
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · have hempty : verticesBelow P h t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hz0 : z = 0 := by
          funext q
          by_contra hq
          obtain ⟨x, y, hxy, hr⟩ := vertexIncidence_pair P q
          have hxq : x.val ∈ q.val := (hr x).mpr (Or.inl rfl)
          have hxm : x.val ∈ verticesBelow P h t :=
            Finset.mem_filter.mpr ⟨x.property, hs q hq x hxq⟩
          rw [hempty] at hxm
          exact Finset.notMem_empty _ hxm
        refine ⟨0, ?_⟩
        simp [hz0]
  intro z hz
  obtain ⟨a, ha, hmax⟩ := P.vertices.exists_max_image h P.vertices_nonempty
  let t := h a + 1
  apply main (verticesBelow P h t).card t rfl z hz
  intro q hq x hxq
  have hle := hmax x.val x.property
  dsimp [t]
  linarith

/-- Every geometric edge cycle of a solid convex polyhedron is a sum of
actual geometric facet boundaries over 𝔽₂. -/
theorem polyhedron_cycle_filling (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∀ z : PolytopeFace P 1 → ZMod 2, (vertexIncidence P).transpose.mulVec z = 0 →
      ∃ c : PolytopeFace P 2 → ZMod 2, (facetIncidence P).mulVec c = z := by
  obtain ⟨h, hinj, hfill⟩ := exists_height_local_cycle_filling P hfull
  exact cycle_filling_of_local P h hinj hfill

/-- Euler's polyhedron formula for every full-dimensional finite convex hull
in Euclidean three-space, counting its actual exposed vertices, edges and facets. -/
theorem polyhedron_euler (P : ConvexPolytope 3) (hfull : P.IsFullDim) : boundaryEuler P = 2 :=
  (polyhedron_euler_eq_two_iff_cycle_filling P hfull).mpr (polyhedron_cycle_filling P hfull)

/-- The equivalent natural-number form of the full geometric Euler formula. -/
theorem polyhedron_vertices_facets_eq_edges_add_two (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) : faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 := by
  have h := polyhedron_euler P hfull
  unfold boundaryEuler at h
  omega

/-- The classical planar edge bound, derived from geometric Euler and
facet incidences for every solid convex polyhedron. -/
theorem polyhedron_edges_le_three_vertices_sub_six (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) : faceCount P 1 ≤ 3 * faceCount P 0 - 6 := by
  have hEuler := polyhedron_vertices_facets_eq_edges_add_two P hfull
  have hfacet := polyhedron_three_facets_le_two_edges P hfull
  omega

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_cycle_filling
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_euler
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_edges_le_three_vertices_sub_six

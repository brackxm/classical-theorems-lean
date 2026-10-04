/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolytopeFaces
import UnicoProofs.Platonici.ConoVertice
import UnicoProofs.Platonici.SecondaFaccetta

/-! Geometric incidence counts for arbitrary convex polygons and solid
polyhedra. All incident objects are genuine exposed faces. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- Finite enumeration of the distinct geometric `k`-faces. -/
def faceFinset {n : ℕ} (P : ConvexPolytope n) (k : ℕ) : Finset (Set (E n)) :=
  (facesOfDim_finite P k).toFinset

@[simp] theorem mem_faceFinset {n : ℕ} (P : ConvexPolytope n) (k : ℕ) (F : Set (E n)) :
    F ∈ faceFinset P k ↔ P.IsFace F ∧ faceDim F = k := by simp [faceFinset, facesOfDim]

@[simp] theorem card_faceFinset {n : ℕ} (P : ConvexPolytope n) (k : ℕ) :
    (faceFinset P k).card = faceCount P k := (Set.ncard_eq_toFinset_card _ (facesOfDim_finite P k)).symm

/-- Exactly the ambient vertices lying in a given geometric face. -/
def faceVertices {n : ℕ} (P : ConvexPolytope n) (F : Set (E n)) : Finset (E n) :=
  P.vertices.filter (· ∈ F)

@[simp] theorem mem_faceVertices (P : ConvexPolytope 3) (F : Set (E 3)) (v : E 3) :
    v ∈ faceVertices P F ↔ v ∈ P.vertices ∧ v ∈ F := by
  simp only [faceVertices, Finset.mem_filter]

/-- Every edge has precisely two vertices, derived from its geometry. -/
theorem edge_vertices_card {n : ℕ} (P : ConvexPolytope n) {e : Set (E n)}
    (he : P.IsFace e) (hd : faceDim e = 1) : (faceVertices P e).card = 2 := by
  obtain ⟨v, hv⟩ := (facePolytope P he).vertices_nonempty
  have hv' : v ∈ P.vertices ∧ v ∈ e := Finset.mem_filter.mp hv
  obtain ⟨w, hwV, hwe, hwv, hseg⟩ := spigolo_segmento P he hd hv'.1 hv'.2
  have hverts : faceVertices P e = {v, w} := by
    ext x
    simp only [faceVertices, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxV, hxe⟩
      have hx := vertice_estremo_in_faccia P he hxV hxe
      rw [hseg, ← convexHull_pair] at hx
      have hxpair : x ∈ ({v, w} : Set (E n)) := extremePoints_convexHull_subset hx
      simpa only [mem_insert_iff, mem_singleton_iff] using hxpair
    · rintro (rfl | rfl)
      · exact hv'
      · exact ⟨hwV, hwe⟩
  rw [hverts]
  simp [hwv.symm]

/-- The edges through a specified vertex. -/
def incidentEdges {n : ℕ} (P : ConvexPolytope n) (v : E n) : Finset (Set (E n)) :=
  (faceFinset P 1).filter (v ∈ ·)

/-- Every vertex of any convex polygon lies on exactly two edges. The polygon
may live in an arbitrary-dimensional Euclidean space. -/
theorem polygon_incident_edges_card {n : ℕ} (P : ConvexPolytope n) (hdim : P.dim = 2)
    {v : E n} (hv : v ∈ P.vertices) : (incidentEdges P v).card = 2 := by
  have hsingle := vertex_isFace P hv
  have hsingleDim : faceDim ({v} : Set (E n)) = 0 := by simp [faceDim]
  obtain ⟨e, he, hsub, hne⟩ := interpolazione P hsingle (by
    change faceDim ({v} : Set (E n)) + 2 ≤ P.dim
    rw [hsingleDim, hdim])
  have helower := faceDim_lt_of_ssubset P hsingle he hsub
  have heupper := faceDim_lt_of_ssubset P he (toSet_isFace P)
    (ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P he, hne⟩)
  have hde : faceDim e = 1 := by change faceDim e < P.dim at heupper; omega
  have hve : v ∈ e := hsub.subset (mem_singleton v)
  obtain ⟨f, hf, hdf, hvf, hfe⟩ := secondo_spigolo P hdim hv he hde hve
  have hall : incidentEdges P v = {e, f} := by
    ext g
    simp only [incidentEdges, Finset.mem_filter, mem_faceFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hg, hdg⟩, hvg⟩
      by_cases hge : g = e
      · exact Or.inl hge
      by_cases hgf : g = f
      · exact Or.inr hgf
      exact False.elim (diamante_poligono P hdim he hde hf hdf hg hdg
        hfe.symm (Ne.symm hge) (Ne.symm hgf) hve hvf hvg)
    · rintro (rfl | rfl)
      · exact ⟨⟨he, hde⟩, hve⟩
      · exact ⟨⟨hf, hdf⟩, hvf⟩
  rw [hall]
  simp [hfe.symm]

/-- Double-counting geometric vertex-edge incidences proves that every convex
polygon has equally many edges and vertices, without prescribing its shape. -/
theorem polygon_faceCount_one {n : ℕ} (P : ConvexPolytope n) (hdim : P.dim = 2) :
    faceCount P 1 = faceCount P 0 := by
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun v : E n => fun e : Set (E n) => v ∈ e)
    (s := P.vertices) (t := faceFinset P 1)
  have hleft : (∑ v ∈ P.vertices, ((faceFinset P 1).bipartiteAbove
      (fun v : E n => fun e : Set (E n) => v ∈ e) v).card) = P.vertices.card * 2 := by
    calc
      _ = ∑ v ∈ P.vertices, 2 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact polygon_incident_edges_card P hdim hv
      _ = _ := by simp
  have hright : (∑ e ∈ faceFinset P 1, (P.vertices.bipartiteBelow
      (fun v : E n => fun e : Set (E n) => v ∈ e) e).card) = faceCount P 1 * 2 := by
    calc
      _ = ∑ e ∈ faceFinset P 1, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        obtain ⟨he, hd⟩ := (mem_faceFinset P 1 e).mp he
        exact edge_vertices_card P he hd
      _ = _ := by simp
  rw [hleft, hright] at hdouble
  rw [faceCount_zero]
  omega

/-- The full geometric Euler relation for every convex polygon. -/
theorem polygon_euler {n : ℕ} (P : ConvexPolytope n) (hdim : P.dim = 2) :
    (faceCount P 0 : ℤ) - (faceCount P 1 : ℤ) + (faceCount P 2 : ℤ) = 1 := by
  rw [polygon_faceCount_one P hdim, ← hdim, faceCount_top]
  omega

/-- The facets containing a given edge. -/
def incidentFacets (P : ConvexPolytope 3) (e : Set (E 3)) : Finset (Set (E 3)) :=
  (faceFinset P 2).filter (e ⊆ ·)

/-- Each edge of every solid convex polyhedron belongs to exactly two facets. -/
theorem polyhedron_incident_facets_card (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {e : Set (E 3)} (he : P.IsFace e) (hde : faceDim e = 1) :
    (incidentFacets P e).card = 2 := by
  have hdim : P.dim = 3 := hfull
  obtain ⟨A, hA, hsub, hne⟩ := interpolazione P he (by change faceDim e + 2 ≤ P.dim; omega)
  have hlower := faceDim_lt_of_ssubset P he hA hsub
  have hupper := faceDim_lt_of_ssubset P hA (toSet_isFace P)
    (ssubset_iff_subset_ne.mpr ⟨face_subset_toSet P hA, hne⟩)
  have hdA : faceDim A = 2 := by change faceDim A < P.dim at hupper; omega
  obtain ⟨B, hB, hdB, heB, hBA⟩ := seconda_faccetta P hfull he hde hA hdA hsub.subset
  obtain ⟨v, hv⟩ := he.2
  obtain ⟨w, hw, hwv⟩ := faccia_ha_secondo_punto hde (v := v)
  have hall : incidentFacets P e = {A, B} := by
    ext C
    simp only [incidentFacets, Finset.mem_filter, mem_faceFinset,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hC, hdC⟩, heC⟩
      exact spigolo_in_due_faccette P v hA hdA hB hdB hC hdC hBA.symm
        (hsub.subset hv) (heB hv) (heC hv) ⟨hsub.subset hw, heB hw⟩ hwv (heC hw)
    · rintro (rfl | rfl)
      · exact ⟨⟨hA, hdA⟩, hsub.subset⟩
      · exact ⟨⟨hB, hdB⟩, heB⟩
  rw [hall]
  simp [hBA.symm]

/-- The total number of edge-facet incidences equals twice the number of edges. -/
theorem polyhedron_edge_facet_handshake (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (∑ F ∈ faceFinset P 2, ((faceFinset P 1).filter (· ⊆ F)).card) =
      2 * faceCount P 1 := by
  have hdouble := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun e F : Set (E 3) => e ⊆ F) (s := faceFinset P 1) (t := faceFinset P 2)
  have hleft : (∑ e ∈ faceFinset P 1, ((faceFinset P 2).bipartiteAbove
      (fun e F : Set (E 3) => e ⊆ F) e).card) = 2 * faceCount P 1 := by
    calc
      _ = ∑ e ∈ faceFinset P 1, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        obtain ⟨he, hd⟩ := (mem_faceFinset P 1 e).mp he
        exact polyhedron_incident_facets_card P hfull he hd
      _ = _ := by simp [Nat.mul_comm]
  exact hdouble.symm.trans hleft

/-- The edges of a geometric face are exactly the ambient edges it contains. -/
theorem facePolytope_edges (P : ConvexPolytope 3) {F : Set (E 3)} (hF : P.IsFace F) :
    faceFinset (facePolytope P hF) 1 = (faceFinset P 1).filter (· ⊆ F) := by
  ext e
  simp only [mem_faceFinset, Finset.mem_filter]
  constructor
  · rintro ⟨he, hd⟩
    refine ⟨⟨isFace_of_facePolytope P hF he, hd⟩, ?_⟩
    have hsub := face_subset_toSet (facePolytope P hF) he
    rwa [facePolytope_toSet P hF] at hsub
  · rintro ⟨⟨he, hd⟩, hsub⟩
    exact ⟨facePolytope_isFace_of P hF he hsub, hd⟩

/-- Every facet has as many incident edges as vertices, since it is itself
an actual convex polygon. -/
theorem facet_edges_eq_vertices (P : ConvexPolytope 3) {F : Set (E 3)}
    (hF : P.IsFace F) (hd : faceDim F = 2) :
    ((faceFinset P 1).filter (· ⊆ F)).card = (faceVertices P F).card := by
  have hdim : (facePolytope P hF).dim = 2 := by
    unfold dim
    rw [facePolytope_toSet P hF]
    exact hd
  rw [← facePolytope_edges P hF, card_faceFinset,
    polygon_faceCount_one _ hdim, faceCount_zero]
  rfl

/-- A finite convex hull needs at least dimension + 1 vertices. -/
theorem vertices_card_ge_dim_succ {n : ℕ} (P : ConvexPolytope n) :
    P.dim + 1 ≤ P.vertices.card := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let : Nonempty {x // x ∈ P.vertices} := ⟨⟨v, hv⟩⟩
  have h := finrank_vectorSpan_range_add_one_le ℝ
    (Subtype.val : {x // x ∈ P.vertices} → E n)
  have hrange : range (Subtype.val : {x // x ∈ P.vertices} → E n) =
      (P.vertices : Set (E n)) := by ext x; simp
  rw [hrange] at h
  unfold dim toSet
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  simpa using h

/-- Every two-dimensional facet has at least three genuine vertices. -/
theorem facet_vertices_ge_three (P : ConvexPolytope 3) {F : Set (E 3)}
    (hF : P.IsFace F) (hd : faceDim F = 2) : 3 ≤ (faceVertices P F).card := by
  have h := vertices_card_ge_dim_succ (facePolytope P hF)
  have hdim : (facePolytope P hF).dim = 2 := by
    unfold dim
    rw [facePolytope_toSet P hF]
    exact hd
  rw [hdim] at h
  exact h

/-- For arbitrary solid convex polyhedra, the total vertex-facet incidence
count also equals twice the number of edges. -/
theorem polyhedron_vertex_facet_handshake (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (∑ F ∈ faceFinset P 2, (faceVertices P F).card) = 2 * faceCount P 1 := by
  rw [← polyhedron_edge_facet_handshake P hfull]
  apply Finset.sum_congr rfl
  intro F hF
  obtain ⟨hF, hd⟩ := (mem_faceFinset P 2 F).mp hF
  exact (facet_edges_eq_vertices P hF hd).symm

/-- The geometric facet-edge bound, with no assumed incidence or Euler identity. -/
theorem polyhedron_three_facets_le_two_edges (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    3 * faceCount P 2 ≤ 2 * faceCount P 1 := by
  calc
    _ = ∑ F ∈ faceFinset P 2, 3 := by simp [Nat.mul_comm]
    _ ≤ ∑ F ∈ faceFinset P 2, (faceVertices P F).card := by
      apply Finset.sum_le_sum
      intro F hF
      obtain ⟨hF, hd⟩ := (mem_faceFinset P 2 F).mp hF
      exact facet_vertices_ge_three P hF hd
    _ = _ := polyhedron_vertex_facet_handshake P hfull

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.edge_vertices_card
#check_upstream ClassicalTheorems.Progress.Euler.polygon_euler
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_incident_facets_card
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_edge_facet_handshake
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_vertex_facet_handshake
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_three_facets_le_two_edges

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolyhedronEuler

/-! Euler's formula for geometric convex pyramids with arbitrary polygonal
bases. A pyramid is specified by a genuine base facet and one apex; no face
counts, incidence data, or Euler identity are assumed. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- All vertices except a single apex lie in a specified geometric base. -/
structure IsPyramid (P : ConvexPolytope 3) (B : Set (E 3)) (a : E 3) : Prop where
  base_face : P.IsFace B
  base_dim : faceDim B = 2
  apex_vertex : a ∈ P.vertices
  apex_not_base : a ∉ B
  vertices : ∀ v ∈ P.vertices, v = a ∨ v ∈ B

/-- A point of the body outside an exposed face also lies outside its affine
span. This derives the pyramid's geometric nondegeneracy. -/
theorem point_notMem_affineSpan_face {n : ℕ} (P : ConvexPolytope n)
    {B : Set (E n)} (hB : P.IsFace B) {a : E n} (ha : a ∈ P.toSet) (haB : a ∉ B) :
    a ∉ affineSpan ℝ B := by
  obtain ⟨l, hl⟩ := hB.1 hB.2
  obtain ⟨b, hb⟩ := hB.2
  have hb' := hb
  rw [hl] at hb'
  have hconst : ∀ x ∈ B, l x = l b := by
    intro x hx
    rw [hl] at hx
    exact le_antisymm (hb'.2 x hx.1) (hx.2 b hb'.1)
  have heq : Set.EqOn (⇑l.toLinearMap.toAffineMap)
      (⇑(AffineMap.const ℝ (E n) (l b))) B := by
    intro x hx
    exact hconst x hx
  intro haspan
  have hla : l a = l b := AffineMap.eqOn_affineSpan (k := ℝ) heq haspan
  apply haB
  rw [hl]
  exact ⟨ha, fun x hx => by rw [hla]; exact hb'.2 x hx⟩

/-- Coning a nonempty set from a point outside its affine span raises affine
dimension by exactly one. -/
theorem faceDim_hull_insert {n : ℕ} {s : Set (E n)} (hs : s.Nonempty)
    {a : E n} (ha : a ∉ affineSpan ℝ s) :
    faceDim (convexHull ℝ (insert a s)) = faceDim s + 1 := by
  have hlt : affineSpan ℝ s < affineSpan ℝ (insert a s) := by
    refine lt_of_le_of_ne (affineSpan_mono ℝ (subset_insert a s)) ?_
    intro heq
    apply ha
    rw [heq]
    exact subset_affineSpan ℝ _ (mem_insert a s)
  have hd := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hlt (hs.affineSpan ℝ))
  rw [direction_affineSpan, direction_affineSpan] at hd
  have hu := finrank_vectorSpan_insert_le_set ℝ s a
  unfold faceDim
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  omega

/-- A face of a pyramid missing the apex is contained in the base. -/
theorem pyramid_face_subset_base (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) {F : Set (E 3)} (hF : P.IsFace F) (haF : a ∉ F) : F ⊆ B := by
  rw [face_eq_hull_vertices P hF]
  apply convexHull_min _ (h.base_face.1.convex (convex_convexHull ℝ _))
  intro v hv
  obtain ⟨hvV, hvF⟩ := Finset.mem_filter.mp hv
  rcases h.vertices v hvV with rfl | hvB
  · exact False.elim (haF hvF)
  · exact hvB

/-- Every facet other than the base contains the apex. -/
theorem pyramid_lateral_contains_apex (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) {F : Set (E 3)} (hF : P.IsFace F)
    (hdF : faceDim F = 2) (hFB : F ≠ B) : a ∈ F := by
  by_contra haF
  have hsub := pyramid_face_subset_base P h hF haF
  have hlt := faceDim_lt_of_ssubset P hF h.base_face
    (ssubset_iff_subset_ne.mpr ⟨hsub, hFB⟩)
  rw [hdF, h.base_dim] at hlt
  omega

/-- The vertices of a lateral facet are its apex and the vertices in its
intersection with the base. -/
theorem pyramid_lateral_vertices (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) {F : Set (E 3)} (hF : P.IsFace F)
    (hdF : faceDim F = 2) (hFB : F ≠ B) :
    faceVertices P F = insert a (faceVertices P (F ∩ B)) := by
  have haF := pyramid_lateral_contains_apex P h hF hdF hFB
  ext v
  simp only [faceVertices, Finset.mem_filter, mem_inter_iff, Finset.mem_insert]
  constructor
  · rintro ⟨hvV, hvF⟩
    rcases h.vertices v hvV with hva | hvB
    · exact Or.inl hva
    · exact Or.inr ⟨hvV, hvF, hvB⟩
  · rintro (rfl | ⟨hvV, hvF, _⟩)
    · exact ⟨h.apex_vertex, haF⟩
    · exact ⟨hvV, hvF⟩

/-- A lateral facet meets the base in a genuine geometric edge. -/
theorem pyramid_lateral_base_edge (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) {F : Set (E 3)} (hF : P.IsFace F)
    (hdF : faceDim F = 2) (hFB : F ≠ B) :
    P.IsFace (F ∩ B) ∧ faceDim (F ∩ B) = 1 := by
  have hv := pyramid_lateral_vertices P h hF hdF hFB
  have hcard := facet_vertices_ge_three P hF hdF
  have hne : (faceVertices P (F ∩ B)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty] at hn
    rw [hv, hn] at hcard
    simp at hcard
  have hI : P.IsFace (F ∩ B) := ⟨hF.1.inter h.base_face.1, by
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, ((mem_faceVertices P _ _).mp hv).2⟩⟩
  have hspan : a ∉ affineSpan ℝ ((faceVertices P (F ∩ B) : Finset (E 3)) : Set (E 3)) := by
    have ha := point_notMem_affineSpan_face P h.base_face
      (subset_convexHull ℝ _ h.apex_vertex) h.apex_not_base
    intro ha'
    apply ha
    apply affineSpan_mono ℝ _ ha'
    intro v hv
    exact ((mem_faceVertices P _ _).mp hv).2.2
  have hd := faceDim_hull_insert hne.to_set hspan
  have hFhull := face_eq_hull_vertices P hF
  change F = convexHull ℝ (faceVertices P F : Set (E 3)) at hFhull
  rw [hv, Finset.coe_insert] at hFhull
  rw [← hFhull, hdF] at hd
  have hIhull := face_eq_hull_vertices P hI
  have hIspan : faceDim (convexHull ℝ (faceVertices P (F ∩ B) : Set (E 3))) =
      faceDim (faceVertices P (F ∩ B) : Set (E 3)) := by
    unfold faceDim
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  change F ∩ B = convexHull ℝ (faceVertices P (F ∩ B) : Set (E 3)) at hIhull
  have hdim := congrArg faceDim hIhull
  rw [hIspan] at hdim
  exact ⟨hI, by omega⟩

/-- Every lateral facet is a triangle, derived from the base edge rather than
included as a combinatorial hypothesis. -/
theorem pyramid_lateral_vertices_card (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) {F : Set (E 3)} (hF : P.IsFace F)
    (hdF : faceDim F = 2) (hFB : F ≠ B) : (faceVertices P F).card = 3 := by
  obtain ⟨hI, hdI⟩ := pyramid_lateral_base_edge P h hF hdF hFB
  rw [pyramid_lateral_vertices P h hF hdF hFB, Finset.card_insert_of_notMem]
  · rw [edge_vertices_card P hI hdI]
  · intro ha
    exact h.apex_not_base ((mem_faceVertices P _ _).mp ha).2.2

/-- Lateral facets correspond bijectively to the edges of the base. -/
theorem pyramid_lateral_facets_card (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {B : Set (E 3)} {a : E 3} (h : IsPyramid P B a) :
    ((faceFinset P 2).erase B).card = (faceVertices P B).card := by
  rw [← facet_edges_eq_vertices P h.base_face h.base_dim]
  apply Finset.card_bij (fun F _ => F ∩ B)
  · intro F hF
    obtain ⟨hFB, hFmem⟩ := Finset.mem_erase.mp hF
    obtain ⟨hFface, hdF⟩ := (mem_faceFinset P 2 F).mp hFmem
    obtain ⟨hI, hdI⟩ := pyramid_lateral_base_edge P h hFface hdF hFB
    exact Finset.mem_filter.mpr ⟨(mem_faceFinset P 1 _).mpr ⟨hI, hdI⟩,
      inter_subset_right⟩
  · intro F hF G hG hIG
    obtain ⟨hFB, hFmem⟩ := Finset.mem_erase.mp hF
    obtain ⟨hGB, hGmem⟩ := Finset.mem_erase.mp hG
    obtain ⟨hFface, hdF⟩ := (mem_faceFinset P 2 F).mp hFmem
    obtain ⟨hGface, hdG⟩ := (mem_faceFinset P 2 G).mp hGmem
    apply face_vertices_injective P hFface hGface
    change faceVertices P F = faceVertices P G
    rw [pyramid_lateral_vertices P h hFface hdF hFB,
      pyramid_lateral_vertices P h hGface hdG hGB, hIG]
  · intro e he
    obtain ⟨hemem, heB⟩ := Finset.mem_filter.mp he
    obtain ⟨heface, hde⟩ := (mem_faceFinset P 1 e).mp hemem
    obtain ⟨F, hF, hdF, heF, hFB⟩ :=
      seconda_faccetta P hfull heface hde h.base_face h.base_dim heB
    refine ⟨F, Finset.mem_erase.mpr ⟨hFB, (mem_faceFinset P 2 F).mpr ⟨hF, hdF⟩⟩, ?_⟩
    obtain ⟨hI, hdI⟩ := pyramid_lateral_base_edge P h hF hdF hFB
    have hsub : e ⊆ F ∩ B := subset_inter heF heB
    by_contra hne
    have hlt := faceDim_lt_of_ssubset P heface hI
      (ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩)
    rw [hde, hdI] at hlt
    omega

/-- The body has one more vertex than its polygonal base. -/
theorem pyramid_vertices_card (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) : P.vertices.card = (faceVertices P B).card + 1 := by
  have hv : P.vertices = insert a (faceVertices P B) := by
    ext v
    simp only [Finset.mem_insert, mem_faceVertices]
    constructor
    · intro hv
      rcases h.vertices v hv with rfl | hvB
      · exact Or.inl rfl
      · exact Or.inr ⟨hv, hvB⟩
    · rintro (rfl | ⟨hv, _⟩)
      · exact h.apex_vertex
      · exact hv
  rw [hv, Finset.card_insert_of_notMem]
  intro ha
  exact h.apex_not_base ((mem_faceVertices P B a).mp ha).2

/-- The actual geometric f-vector of a pyramid with an m-vertex base is
(m+1, 2m, m+1), for any convex polygonal base. -/
theorem pyramid_face_counts (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {B : Set (E 3)} {a : E 3} (h : IsPyramid P B a) :
    faceCount P 0 = (faceVertices P B).card + 1 ∧
    faceCount P 1 = 2 * (faceVertices P B).card ∧
    faceCount P 2 = (faceVertices P B).card + 1 := by
  have hBmem : B ∈ faceFinset P 2 :=
    (mem_faceFinset P 2 B).mpr ⟨h.base_face, h.base_dim⟩
  have hlat := pyramid_lateral_facets_card P hfull h
  have hF := Finset.card_erase_add_one hBmem
  rw [hlat, card_faceFinset] at hF
  have hsum : (∑ F ∈ (faceFinset P 2).erase B, (faceVertices P F).card) =
      3 * (faceVertices P B).card := by
    calc
      _ = ∑ F ∈ (faceFinset P 2).erase B, 3 := by
        apply Finset.sum_congr rfl
        intro F hF
        obtain ⟨hFB, hFmem⟩ := Finset.mem_erase.mp hF
        obtain ⟨hFface, hdF⟩ := (mem_faceFinset P 2 F).mp hFmem
        exact pyramid_lateral_vertices_card P h hFface hdF hFB
      _ = _ := by simp [hlat, Nat.mul_comm]
  have hE := Finset.add_sum_erase (faceFinset P 2)
    (fun F => (faceVertices P F).card) hBmem
  rw [hsum, polyhedron_vertex_facet_handshake P hfull] at hE
  exact ⟨by rw [faceCount_zero, pyramid_vertices_card P h], by omega, hF.symm⟩

/-- A polygonal base and an apex outside it force the pyramid to be solid. -/
theorem IsPyramid.isFullDim (P : ConvexPolytope 3) {B : Set (E 3)} {a : E 3}
    (h : IsPyramid P B a) : P.IsFullDim := by
  have haT : a ∈ P.toSet := subset_convexHull ℝ _ h.apex_vertex
  have haB := point_notMem_affineSpan_face P h.base_face haT h.apex_not_base
  have hd := faceDim_hull_insert h.base_face.2 haB
  rw [h.base_dim] at hd
  have hsub : convexHull ℝ (insert a B) ⊆ P.toSet := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    rintro x (rfl | hx)
    · exact haT
    · exact face_subset_toSet P h.base_face hx
  have hlo := Submodule.finrank_mono (vectorSpan_mono ℝ hsub)
  change faceDim (convexHull ℝ (insert a B)) ≤ P.dim at hlo
  rw [hd] at hlo
  have hhi : P.dim ≤ 3 := by
    have ht := Submodule.finrank_le (vectorSpan ℝ P.toSet)
    simpa [dim, E] using ht
  show P.dim = 3
  omega

/-- Euler's polyhedron formula for every solid convex pyramid. -/
theorem pyramid_euler (P : ConvexPolytope 3)
    {B : Set (E 3)} {a : E 3} (h : IsPyramid P B a) : boundaryEuler P = 2 :=
  polyhedron_euler P (h.isFullDim P)

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.point_notMem_affineSpan_face
#check_upstream ClassicalTheorems.Progress.Euler.faceDim_hull_insert
#check_upstream ClassicalTheorems.Progress.Euler.pyramid_lateral_base_edge
#check_upstream ClassicalTheorems.Progress.Euler.pyramid_lateral_facets_card
#check_upstream ClassicalTheorems.Progress.Euler.pyramid_face_counts
#check_upstream ClassicalTheorems.Progress.Euler.IsPyramid.isFullDim
#check_upstream ClassicalTheorems.Progress.Euler.pyramid_euler

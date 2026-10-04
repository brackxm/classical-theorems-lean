/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.DescendingVertexFigure
import ClassicalTheorems.Progress.IncidenceFilling

/-! Filling even chains in descending vertex figures using genuine facets
whose other vertices all have smaller height. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- Edges from a vertex to a vertex of strictly smaller height. -/
abbrev DescendingEdge (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ) :=
  {e : SpigoloPer P v.val // h (SpigoloPer.altro P v.val v.property e) < h v.val}

noncomputable instance (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ) :
    Fintype (DescendingEdge P v h) := Fintype.ofFinite _

/-- Facets for which the specified vertex is the unique highest vertex. -/
abbrev DescendingFacet (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ) :=
  {F : PolytopeFace P 2 // v.val ∈ F.val ∧
    ∀ x ∈ P.vertices, x ∈ F.val → x ≠ v.val → h x < h v.val}

/-- The actual local facet-edge incidence matrix. -/
def descendingIncidence (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ) :
    Matrix (DescendingFacet P v h) (DescendingEdge P v h) (ZMod 2) :=
  incidenceMatrix (fun F e => e.val.val ⊆ F.val.val)

/-- Exactly two descending edges of a descending facet meet its top vertex. -/
theorem descendingIncidence_pair (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (F : DescendingFacet P v h) :
    ∃ e d : DescendingEdge P v h, e ≠ d ∧ ∀ q : DescendingEdge P v h,
      q.val.val ⊆ F.val.val ↔ q = e ∨ q = d := by
  obtain ⟨hF, hdF⟩ := (mem_faceFinset P 2 _).mp F.val.property
  let s := (faceFinset P 1).filter (fun e => v.val ∈ e ∧ e ⊆ F.val.val)
  have hcard : s.card = 2 := facet_vertex_edges_card P hF hdF v.property F.property.1
  obtain ⟨A, B, hAB, hs⟩ := Finset.card_eq_two.mp hcard
  have hA : A ∈ s := by rw [hs]; simp
  have hB : B ∈ s := by rw [hs]; simp
  have hA' : (P.IsFace A ∧ faceDim A = 1) ∧ v.val ∈ A ∧ A ⊆ F.val.val := by
    simpa [s] using hA
  have hB' : (P.IsFace B ∧ faceDim B = 1) ∧ v.val ∈ B ∧ B ⊆ F.val.val := by
    simpa [s] using hB
  let e : SpigoloPer P v.val := ⟨A, hA'.1.1, hA'.1.2, hA'.2.1⟩
  let d : SpigoloPer P v.val := ⟨B, hB'.1.1, hB'.1.2, hB'.2.1⟩
  have he : h (SpigoloPer.altro P v.val v.property e) < h v.val := by
    have ha := SpigoloPer.altro_spec P v.val v.property e
    exact F.property.2 _ ha.1 (hA'.2.2 ha.2.1) ha.2.2.1
  have hd : h (SpigoloPer.altro P v.val v.property d) < h v.val := by
    have ha := SpigoloPer.altro_spec P v.val v.property d
    exact F.property.2 _ ha.1 (hB'.2.2 ha.2.1) ha.2.2.1
  refine ⟨⟨e, he⟩, ⟨d, hd⟩, fun heq => hAB (congrArg (fun x => x.val.val) heq), ?_⟩
  intro q
  have hmem : q.val.val ∈ s ↔ q.val.val = A ∨ q.val.val = B := by rw [hs]; simp
  have hiff : q.val.val ⊆ F.val.val ↔ q.val.val = A ∨ q.val.val = B := by
    simpa [s, q.val.property.1, q.val.property.2.1, q.val.property.2.2] using hmem
  constructor
  · intro hq
    rcases hiff.mp hq with hqA | hqB
    · exact Or.inl (Subtype.ext (Subtype.ext hqA))
    · exact Or.inr (Subtype.ext (Subtype.ext hqB))
  · rintro (rfl | rfl)
    · exact hA'.2.2
    · exact hB'.2.2

/-- The geometric descending paths propagate equality of coefficients
through the local facet-edge incidence system. -/
theorem descendingIncidence_connected (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ)
    (hpaths : ∀ e d : SpigoloPer P v.val,
      h (SpigoloPer.altro P v.val v.property e) < h v.val →
      h (SpigoloPer.altro P v.val v.property d) < h v.val →
      Relation.ReflTransGen (descendingFacetAdjacent P v h) e d)
    (f : DescendingEdge P v h → ZMod 2)
    (hloc : ∀ (F : DescendingFacet P v h) (e d : DescendingEdge P v h),
      e.val.val ⊆ F.val.val → d.val.val ⊆ F.val.val → f e = f d) :
    ∀ e d, f e = f d := by
  intro e d
  have key : ∀ a, Relation.ReflTransGen (descendingFacetAdjacent P v h) a d.val →
      ∀ ha : h (SpigoloPer.altro P v.val v.property a) < h v.val, f ⟨a, ha⟩ = f d := by
    intro a hwalk
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => intro ha; rfl
    | @head a b hstep htail ih =>
      intro ha
      obtain ⟨hne, F, hF, hdF, heF, hdFsub, htop⟩ := hstep
      have hvF : v.val ∈ F := heF a.property.2.2
      let F' : DescendingFacet P v h :=
        ⟨⟨F, (mem_faceFinset P 2 F).mpr ⟨hF, hdF⟩⟩, hvF, htop⟩
      have hb : h (SpigoloPer.altro P v.val v.property b) < h v.val := by
        have ha := SpigoloPer.altro_spec P v.val v.property b
        exact htop _ ha.1 (hdFsub ha.2.1) ha.2.2.1
      exact (hloc F' ⟨_, ha⟩ ⟨b, hb⟩ heF hdFsub).trans (ih hb)
  exact key e.val (hpaths e.val d.val e.property d.property) e.property

/-- Every even coefficient chain on descending edges can be filled locally
by facets whose other vertices all have strictly smaller height. -/
theorem descending_even_chain_filling (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ)
    (hpaths : ∀ e d : SpigoloPer P v.val,
      h (SpigoloPer.altro P v.val v.property e) < h v.val →
      h (SpigoloPer.altro P v.val v.property d) < h v.val →
      Relation.ReflTransGen (descendingFacetAdjacent P v h) e d)
    (z : DescendingEdge P v h → ZMod 2) (hz : ∑ e, z e = 0) :
    ∃ c : DescendingFacet P v h → ZMod 2, (descendingIncidence P v h).transpose.mulVec c = z := by
  by_cases hne : Nonempty (DescendingEdge P v h)
  · let : Nonempty (DescendingEdge P v h) := hne
    exact incidence_fill_even (fun (F : DescendingFacet P v h) (e : DescendingEdge P v h) =>
      e.val.val ⊆ F.val.val) (descendingIncidence_pair P v h)
      (descendingIncidence_connected P v h hpaths) z hz
  · refine ⟨0, ?_⟩
    funext e
    exact False.elim (hne ⟨e⟩)

/-- Every solid convex polyhedron has a height for which the local filling
step is available at every vertex. No cycle-filling hypothesis is assumed. -/
theorem exists_height_local_cycle_filling (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∃ h : E 3 →L[ℝ] ℝ, Set.InjOn h (P.vertices : Set (E 3)) ∧
      ∀ (v : PolytopeVertex P) (z : DescendingEdge P v h → ZMod 2),
        (∑ e, z e) = 0 → ∃ c : DescendingFacet P v h → ZMod 2,
          (descendingIncidence P v h).transpose.mulVec c = z := by
  obtain ⟨h, hinj, hpaths⟩ := exists_height_descending_facets_connected P hfull
  exact ⟨h, hinj, fun v z hz => descending_even_chain_filling P v h (hpaths v) z hz⟩

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.descending_even_chain_filling
#check_upstream ClassicalTheorems.Progress.Euler.exists_height_local_cycle_filling

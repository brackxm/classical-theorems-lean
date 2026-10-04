/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolytopeEulerBound
import Mathlib.Algebra.Module.Submodule.Union

/-! Generic heights and connectivity of descending geometric vertex figures.
These are steps toward filling edge cycles by geometric facet boundaries. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
open scoped RealInnerProductSpace
namespace ClassicalTheorems.Progress.Euler

/-- A continuous linear height can separate every pair in a finite set of
Euclidean points. It is obtained by avoiding finitely many proper kernels. -/
theorem exists_height_injOn {n : ℕ} (s : Finset (E n)) :
    ∃ h : E n →L[ℝ] ℝ, Set.InjOn h (s : Set (E n)) := by
  let I := {p : s × s // p.1.val ≠ p.2.val}
  let f (i : I) : Module.Dual ℝ (E n) :=
    (innerSL ℝ (i.val.1.val - i.val.2.val)).toLinearMap
  have hf (i : I) : ∃ x, f i x ≠ 0 := by
    refine ⟨i.val.1.val - i.val.2.val, ?_⟩
    exact inner_self_ne_zero.mpr (sub_ne_zero.mpr i.property)
  obtain ⟨w, hw⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨innerSL ℝ w, ?_⟩
  intro x hx y hy heq
  by_contra hxy
  let i : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
  have hzero : (innerSL ℝ w) (x - y) = 0 := by rw [map_sub, heq, sub_self]
  apply hw i
  change ⟪x - y, w⟫ = 0
  rw [real_inner_comm]
  exact hzero

/-- The local-global principle gives a monotone path to a unique maximum. -/
theorem monotone_simplex_walk {α : Type*} [DecidableEq α]
    (X : Finset α) (adj : α → α → Prop) (φ : α → ℝ)
    (hlg : ∀ x ∈ X, (∀ y ∈ X, adj x y → φ y ≤ φ x) → ∀ z ∈ X, φ z ≤ φ x)
    {xs : α} (hxs : xs ∈ X) (hunique : ∀ z ∈ X, z ≠ xs → φ z < φ xs)
    {x : α} (hx : x ∈ X) :
    Relation.ReflTransGen (fun a b => b ∈ X ∧ adj a b ∧ φ a ≤ φ b) x xs := by
  apply camminata_del_simplesso X (fun a b => adj a b ∧ φ a ≤ φ b) φ
    ?_ hxs hunique hx
  intro a ha hloc z hz
  apply hlg a ha _ z hz
  intro b hb hab
  by_cases hle : φ b ≤ φ a
  · exact hle
  · exact hloc b hb ⟨hab, le_of_lt (lt_of_not_ge hle)⟩

/-- A monotone path that starts above a threshold stays above it. -/
theorem monotone_walk_above {α : Type*} (X : Finset α) (adj : α → α → Prop)
    (φ : α → ℝ) {t : ℝ} {x y : α}
    (hx : t < φ x)
    (hwalk : Relation.ReflTransGen (fun a b => b ∈ X ∧ adj a b ∧ φ a ≤ φ b) x y) :
    t < φ y ∧ Relation.ReflTransGen
      (fun a b => adj a b ∧ t < φ a ∧ t < φ b) x y := by
  induction hwalk with
  | refl => exact ⟨hx, .refl⟩
  | tail _ hstep ih =>
    have hbelow := lt_of_lt_of_le ih.1 hstep.2.2
    exact ⟨hbelow, ih.2.tail ⟨hstep.2.1, ih.1, hbelow⟩⟩

/-- A small separating section of the actual polyhedron at a vertex. -/
structure VertexSlice (P : ConvexPolytope 3) (v : E 3) where
  functional : E 3 →L[ℝ] ℝ
  level : ℝ
  below_vertex : level < functional v
  above_others : ∀ u ∈ P.vertices, u ≠ v → functional u < level

/-- Choose the licensed geometric separating section at each vertex. -/
def vertexSlice (P : ConvexPolytope 3) (hfull : P.IsFullDim) (v : PolytopeVertex P) :
    VertexSlice P v.val :=
  let h := esiste_livello_separatore P hfull v.property
  { functional := h.choose
    level := h.choose_spec.choose
    below_vertex := h.choose_spec.choose_spec.1
    above_others := h.choose_spec.choose_spec.2 }

/-- The actual section point on an edge through a vertex. -/
def slicePoint (P : ConvexPolytope 3) (v : PolytopeVertex P) (s : VertexSlice P v.val)
    (e : SpigoloPer P v.val) : E 3 :=
  SpigoloPer.taglio P v.val v.property s.functional s.level e

/-- Distinct incident edges give distinct points of a separating section. -/
theorem slicePoint_injective (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (s : VertexSlice P v.val) : Function.Injective (slicePoint P v s) := by
  intro e d heq
  by_contra hed
  exact tagli_distinti P v.property s.functional s.level s.below_vertex e d hed
    (s.above_others _ (SpigoloPer.altro_spec P v.val v.property e).1
      (SpigoloPer.altro_spec P v.val v.property e).2.2.1)
    (s.above_others _ (SpigoloPer.altro_spec P v.val v.property d).1
      (SpigoloPer.altro_spec P v.val v.property d).2.2.1) heq

/-- All vertex-section points form a finite set. -/
def sliceCloud (P : ConvexPolytope 3) (hfull : P.IsFullDim) : Finset (E 3) :=
  (Set.finite_range (fun a : (v : PolytopeVertex P) × SpigoloPer P v.val =>
    slicePoint P a.1 (vertexSlice P hfull a.1) a.2)).toFinset

/-- One height separates all polyhedron vertices and all the section points
at every vertex, so the subsequent monotone walks have unique extrema. -/
theorem exists_generic_polytope_height (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∃ h : E 3 →L[ℝ] ℝ, Set.InjOn h (P.vertices : Set (E 3)) ∧
      ∀ v : PolytopeVertex P,
        Function.Injective (fun e => h (slicePoint P v (vertexSlice P hfull v) e)) := by
  obtain ⟨h, hinj⟩ := exists_height_injOn (P.vertices ∪ sliceCloud P hfull)
  refine ⟨h, hinj.mono (by intro x hx; exact Finset.mem_union_left _ hx), ?_⟩
  intro v e d heq
  apply slicePoint_injective P v (vertexSlice P hfull v)
  apply hinj _ _ heq
  · apply Finset.mem_union_right
    exact (Set.finite_range _).mem_toFinset.mpr ⟨⟨v, e⟩, rfl⟩
  · apply Finset.mem_union_right
    exact (Set.finite_range _).mem_toFinset.mpr ⟨⟨v, d⟩, rfl⟩

/-- Adjacency between different edges through a vertex, via a common facet. -/
def fanAdjacent (P : ConvexPolytope 3) (v : E 3) (e d : SpigoloPer P v) : Prop :=
  e ≠ d ∧ CondividonoFaccetta P v e d

/-- The imported geometric local-global principle on a separating section,
expressed using the actual incident-edge adjacency. -/
theorem slice_height_local_global (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (v : PolytopeVertex P) (s : VertexSlice P v.val) (h : E 3 →L[ℝ] ℝ)
    (e : SpigoloPer P v.val)
    (hloc : ∀ d, fanAdjacent P v.val e d → h (slicePoint P v s d) ≤ h (slicePoint P v s e)) :
    ∀ d, h (slicePoint P v s d) ≤ h (slicePoint P v s e) := by
  let D := stellaSpigolo P hfull v.property e
  have hA := hloc D.eA ⟨D.heAne.symm, D.A, D.hA, D.hdA, D.heA, D.heAA⟩
  have hB := hloc D.eB ⟨D.heBne.symm, D.B, D.hB, D.hdB, D.heB, D.heBB⟩
  intro d
  have hd := SpigoloPer.taglio_fatti P v.val v.property s.functional s.level
    s.below_vertex d (s.above_others _ (SpigoloPer.altro_spec P v.val v.property d).1
      (SpigoloPer.altro_spec P v.val v.property d).2.2.1)
  exact locale_globale_taglio P v.property s.functional s.level s.below_vertex
    s.above_others e D h hA hB (slicePoint P v s d)
    ⟨face_subset_toSet P d.property.1 hd.1, hd.2.1⟩

/-- The section point is below its vertex exactly when the other endpoint
of the corresponding geometric edge is below the vertex. -/
theorem slicePoint_down_iff (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (s : VertexSlice P v.val) (h : E 3 →L[ℝ] ℝ) (e : SpigoloPer P v.val) :
    h (slicePoint P v s e) < h v.val ↔ h (SpigoloPer.altro P v.val v.property e) < h v.val := by
  let a := SpigoloPer.altro P v.val v.property e
  let t := (s.functional v.val - s.level) / (s.functional v.val - s.functional a)
  have hal : s.functional a < s.level :=
    s.above_others a (SpigoloPer.altro_spec P v.val v.property e).1
      (SpigoloPer.altro_spec P v.val v.property e).2.2.1
  have ht : 0 < t := div_pos (by linarith [s.below_vertex])
    (by linarith [s.below_vertex])
  have heq : h (slicePoint P v s e) = h v.val + t * (h a - h v.val) := by
    simp only [slicePoint, SpigoloPer.taglio, map_add, map_smul, map_sub, smul_eq_mul, a, t]
  rw [heq]
  constructor
  · intro hx
    by_contra ha
    have ha' : 0 ≤ h a - h v.val := by change ¬h a < h v.val at ha; linarith
    have hp := mul_nonneg ht.le ha'
    linarith
  · intro ha
    have ha' : h a - h v.val < 0 := by exact sub_lt_zero.mpr ha
    have hp := mul_neg_of_pos_of_neg ht ha'
    linarith

/-- Adjacency inside the descending part of a geometric vertex figure. -/
def descendingFanAdjacent (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (e d : SpigoloPer P v.val) : Prop :=
  fanAdjacent P v.val e d ∧
    h (SpigoloPer.altro P v.val v.property e) < h v.val ∧
    h (SpigoloPer.altro P v.val v.property d) < h v.val

/-- Reverse a path in a symmetric relation. -/
theorem reverse_symmetric_walk {α : Type*} {r : α → α → Prop}
    (hsym : ∀ ⦃x y⦄, r x y → r y x) {x y : α} (hwalk : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction hwalk with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head (hsym hstep)

/-- The descending part of every vertex figure is connected for any height
that separates the section points. The paths use actual geometric facets. -/
theorem descending_fan_connected (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (v : PolytopeVertex P) (s : VertexSlice P v.val) (h : E 3 →L[ℝ] ℝ)
    (hinj : Function.Injective (fun e => h (slicePoint P v s e)))
    (e d : SpigoloPer P v.val)
    (he : h (SpigoloPer.altro P v.val v.property e) < h v.val)
    (hd : h (SpigoloPer.altro P v.val v.property d) < h v.val) :
    Relation.ReflTransGen (descendingFanAdjacent P v h) e d := by
  let : Fintype (SpigoloPer P v.val) := Fintype.ofFinite _
  let X : Finset (SpigoloPer P v.val) := Finset.univ
  let φ : SpigoloPer P v.val → ℝ := fun a => -h (slicePoint P v s a)
  obtain ⟨m, hm, hmax⟩ := X.exists_max_image φ ⟨e, Finset.mem_univ e⟩
  have hunique : ∀ z ∈ X, z ≠ m → φ z < φ m := by
    intro z hz hzm
    rcases lt_or_eq_of_le (hmax z hz) with hlt | heq
    · exact hlt
    · apply False.elim
      apply hzm
      exact hinj (neg_injective heq)
  have hlg : ∀ a ∈ X, (∀ b ∈ X, fanAdjacent P v.val a b → φ b ≤ φ a) →
      ∀ z ∈ X, φ z ≤ φ a := by
    intro a ha hloc z hz
    exact slice_height_local_global P hfull v s (-h) a
      (fun b hab => hloc b (Finset.mem_univ b) hab) z
  have path : ∀ a, h (SpigoloPer.altro P v.val v.property a) < h v.val →
      Relation.ReflTransGen (descendingFanAdjacent P v h) a m := by
    intro a ha
    have hcut := (slicePoint_down_iff P v s h a).mpr ha
    have hstart : -h v.val < φ a := by dsimp [φ]; linarith
    have hwalk := monotone_simplex_walk X (fanAdjacent P v.val) φ hlg hm hunique
      (Finset.mem_univ a)
    have hrestricted := (monotone_walk_above X (fanAdjacent P v.val) φ hstart hwalk).2
    apply Relation.ReflTransGen.mono _ _ _ hrestricted
    intro a b hab
    refine ⟨hab.1, (slicePoint_down_iff P v s h a).mp ?_,
      (slicePoint_down_iff P v s h b).mp ?_⟩
    · dsimp [φ] at hab
      linarith [hab.2.1]
    · dsimp [φ] at hab
      linarith [hab.2.2]
  have hsym : ∀ ⦃a b⦄, descendingFanAdjacent P v h a b → descendingFanAdjacent P v h b a := by
    rintro a b ⟨⟨hne, F, hF, hdF, haF, hbF⟩, ha, hb⟩
    exact ⟨⟨hne.symm, F, hF, hdF, hbF, haF⟩, hb, ha⟩
  exact (path e he).trans (reverse_symmetric_walk hsym (path d hd))

/-- If both edges of a polygonal facet through a vertex descend, that vertex
maximizes the height on the entire facet. -/
theorem descending_facet_maximum (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (e d : SpigoloPer P v.val) (hne : e ≠ d)
    {F : Set (E 3)} (hF : P.IsFace F) (hdF : faceDim F = 2)
    (heF : e.val ⊆ F) (hdFsub : d.val ⊆ F)
    (he : h (SpigoloPer.altro P v.val v.property e) < h v.val)
    (hd : h (SpigoloPer.altro P v.val v.property d) < h v.val) :
    ∀ x ∈ F, h x ≤ h v.val := by
  let Q := facePolytope P hF
  have hQdim : Q.dim = 2 := by
    unfold dim
    rw [facePolytope_toSet P hF]
    exact hdF
  have hvF : v.val ∈ F := heF e.property.2.2
  have hvQ : v.val ∈ Q.vertices := (mem_faceVertices P F v.val).mpr ⟨v.property, hvF⟩
  have heQ := facePolytope_isFace_of P hF e.property.1 heF
  have hdQ := facePolytope_isFace_of P hF d.property.1 hdFsub
  have hneval : e.val ≠ d.val := fun heq => hne (Subtype.ext heq)
  have hae := SpigoloPer.altro_spec P v.val v.property e
  have had := SpigoloPer.altro_spec P v.val v.property d
  have hglobal := locale_globale Q hQdim hvQ heQ e.property.2.1 hdQ d.property.2.1
    hneval hae.2.1 hae.2.2.1 hae.2.2.2 had.2.1 had.2.2.1 had.2.2.2
    e.property.2.2 d.property.2.2 h he.le hd.le
  intro x hx
  apply hglobal x
  change x ∈ (facePolytope P hF).toSet
  rwa [facePolytope_toSet P hF]

/-- Adjacency of descending edges through a facet whose other vertices are
strictly below the original vertex. These facets can be used in cycle elimination. -/
def descendingFacetAdjacent (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (e d : SpigoloPer P v.val) : Prop :=
  e ≠ d ∧ ∃ F : Set (E 3), P.IsFace F ∧ faceDim F = 2 ∧ e.val ⊆ F ∧ d.val ⊆ F ∧
    ∀ x ∈ P.vertices, x ∈ F → x ≠ v.val → h x < h v.val

/-- Descending fan adjacency uses only facets that stay below the vertex,
when the height separates the actual polyhedron vertices. -/
theorem descending_fan_to_facets (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (hinj : Set.InjOn h (P.vertices : Set (E 3)))
    {e d : SpigoloPer P v.val} (hadj : descendingFanAdjacent P v h e d) :
    descendingFacetAdjacent P v h e d := by
  obtain ⟨⟨hne, F, hF, hdF, heF, hdFsub⟩, he, hd⟩ := hadj
  refine ⟨hne, F, hF, hdF, heF, hdFsub, ?_⟩
  intro x hx hxF hxv
  have hle := descending_facet_maximum P v h e d hne hF hdF heF hdFsub he hd x hxF
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact False.elim (hxv (hinj hx v.property heq))

/-- Every solid convex polyhedron admits one generic height for which the
following holds at every vertex: any two descending edges can be joined
through actual facets whose remaining vertices all lie strictly lower.
This is the geometric local step needed to eliminate the top of an edge cycle. -/
theorem exists_height_descending_facets_connected (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) :
    ∃ h : E 3 →L[ℝ] ℝ, Set.InjOn h (P.vertices : Set (E 3)) ∧
      ∀ (v : PolytopeVertex P) (e d : SpigoloPer P v.val),
        h (SpigoloPer.altro P v.val v.property e) < h v.val →
        h (SpigoloPer.altro P v.val v.property d) < h v.val →
        Relation.ReflTransGen (descendingFacetAdjacent P v h) e d := by
  obtain ⟨h, hinj, hcuts⟩ := exists_generic_polytope_height P hfull
  refine ⟨h, hinj, ?_⟩
  intro v e d he hd
  have hwalk := descending_fan_connected P hfull v (vertexSlice P hfull v) h (hcuts v) e d he hd
  exact Relation.ReflTransGen.mono (fun _ _ hadj => descending_fan_to_facets P v h hinj hadj)
    _ _ hwalk

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.exists_height_injOn
#check_upstream ClassicalTheorems.Progress.Euler.exists_generic_polytope_height
#check_upstream ClassicalTheorems.Progress.Euler.descending_fan_connected
#check_upstream ClassicalTheorems.Progress.Euler.descending_facet_maximum
#check_upstream ClassicalTheorems.Progress.Euler.exists_height_descending_facets_connected

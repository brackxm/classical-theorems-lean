/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolytopeIncidence
import UnicoProofs.Platonici.Connessa
import Mathlib.LinearAlgebra.Matrix.Rank

/-! A global Euler bound from the actual geometric incidence matrices.
Connectivity determines both incidence ranks over the field with two elements.
Polygon incidences give boundary-of-boundary zero, hence V - E + F ≤ 2.
No Euler identity, abstract surface embedding, or planarity is assumed. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- An incidence matrix over the field with two elements. -/
def incidenceMatrix {α β : Type*} (r : β → α → Prop) : Matrix β α (ZMod 2) :=
  fun e v => if r e v then 1 else 0

/-- A row incident to precisely two objects evaluates to their coefficient sum. -/
theorem incidence_mulVec_pair {α β : Type*} [Fintype α] (r : β → α → Prop)
    (e : β) {x y : α} (hxy : x ≠ y) (hr : ∀ v, r e v ↔ v = x ∨ v = y)
    (f : α → ZMod 2) : (incidenceMatrix r).mulVec f e = f x + f y := by
  have hfilter : Finset.univ.filter (r e) = {x, y} := by
    ext v
    simp [hr]
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hfilter, Finset.sum_pair hxy]

/-- For a connected incidence system with two distinct objects per row,
the only zero-boundary coefficient functions are the constants. -/
theorem incidence_ker {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : β → α → Prop)
    (hpair : ∀ e, ∃ x y, x ≠ y ∧ ∀ v, r e v ↔ v = x ∨ v = y)
    (hconn : ∀ f : α → ZMod 2,
      (∀ e x y, r e x → r e y → f x = f y) → ∀ x y, f x = f y) :
    LinearMap.ker (incidenceMatrix r).mulVecLin =
      Submodule.span (ZMod 2) {fun _ : α => (1 : ZMod 2)} := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hf
    have hlocal : ∀ e x y, r e x → r e y → f x = f y := by
      intro e x y hx hy
      obtain ⟨u, v, huv, hr⟩ := hpair e
      have hsum : f u + f v = 0 := by
        rw [← incidence_mulVec_pair r e huv hr f]
        exact congrFun hf e
      have heq : f u = f v := CharTwo.add_eq_zero.mp hsum
      rcases (hr x).mp hx with rfl | rfl <;>
        rcases (hr y).mp hy with rfl | rfl <;> simp_all
    let x : α := Classical.arbitrary α
    refine ⟨f x, ?_⟩
    funext y
    simpa using hconn f hlocal x y
  · rintro ⟨c, rfl⟩
    ext e
    obtain ⟨x, y, hxy, hr⟩ := hpair e
    change (incidenceMatrix r).mulVec (c • (fun _ : α => (1 : ZMod 2))) e = 0
    rw [incidence_mulVec_pair r e hxy hr]
    simp [CharTwo.add_self_eq_zero]

/-- The rank of a connected two-object incidence matrix is one less than
the number of objects. -/
theorem incidence_rank {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (r : β → α → Prop)
    (hpair : ∀ e, ∃ x y, x ≠ y ∧ ∀ v, r e v ↔ v = x ∨ v = y)
    (hconn : ∀ f : α → ZMod 2,
      (∀ e x y, r e x → r e y → f x = f y) → ∀ x y, f x = f y) :
    (incidenceMatrix r).rank + 1 = Fintype.card α := by
  have hne : (fun _ : α => (1 : ZMod 2)) ≠ 0 := by
    intro heq
    have h := congrFun heq (Classical.arbitrary α)
    norm_num at h
  have h := (incidenceMatrix r).mulVecLin.finrank_range_add_finrank_ker
  rw [incidence_ker r hpair hconn, finrank_span_singleton hne,
    Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- Finite types of actual geometric vertices and faces. -/
abbrev PolytopeVertex (P : ConvexPolytope 3) := {v // v ∈ P.vertices}
abbrev PolytopeFace (P : ConvexPolytope 3) (k : ℕ) := {F // F ∈ faceFinset P k}

@[simp] theorem card_polytopeFace (P : ConvexPolytope 3) (k : ℕ) :
    Fintype.card (PolytopeFace P k) = faceCount P k := by simp

/-- Geometric edge-vertex incidences. -/
def vertexIncidence (P : ConvexPolytope 3) :
    Matrix (PolytopeFace P 1) (PolytopeVertex P) (ZMod 2) :=
  incidenceMatrix (fun e v => v.val ∈ e.val)

/-- Geometric edge-facet incidences. -/
def facetIncidence (P : ConvexPolytope 3) :
    Matrix (PolytopeFace P 1) (PolytopeFace P 2) (ZMod 2) :=
  incidenceMatrix (fun e F => e.val ⊆ F.val)

/-- Two ambient objects in a finite subset give two objects of the larger
finite subtype, with precisely the same incidence predicate. -/
theorem finset_subtype_pair {α : Type*} (s t : Finset α) (ht : t ⊆ s)
    (hcard : t.card = 2) :
    ∃ x y : {v // v ∈ s}, x ≠ y ∧ ∀ v : {v // v ∈ s},
      v.val ∈ t ↔ v = x ∨ v = y := by
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard
  have hx : x ∈ s := ht (by rw [hset]; simp)
  have hy : y ∈ s := ht (by rw [hset]; simp)
  refine ⟨⟨x, hx⟩, ⟨y, hy⟩, fun heq => hxy (congrArg Subtype.val heq), ?_⟩
  intro v
  rw [hset]
  simp [Subtype.ext_iff]

/-- Each geometric edge is incident to exactly two different vertices. -/
theorem vertexIncidence_pair (P : ConvexPolytope 3) (e : PolytopeFace P 1) :
    ∃ x y : PolytopeVertex P, x ≠ y ∧ ∀ v : PolytopeVertex P,
      v.val ∈ e.val ↔ v = x ∨ v = y := by
  obtain ⟨he, hd⟩ := (mem_faceFinset P 1 _).mp e.property
  obtain ⟨x, y, hxy, hr⟩ := finset_subtype_pair P.vertices (faceVertices P e.val)
    (Finset.filter_subset _ _) (edge_vertices_card P he hd)
  refine ⟨x, y, hxy, ?_⟩
  intro v
  simpa only [mem_faceVertices, v.property, true_and] using hr v

/-- Each geometric edge is incident to exactly two different facets. -/
theorem facetIncidence_pair (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (e : PolytopeFace P 1) :
    ∃ A B : PolytopeFace P 2, A ≠ B ∧ ∀ F : PolytopeFace P 2,
      e.val ⊆ F.val ↔ F = A ∨ F = B := by
  obtain ⟨he, hd⟩ := (mem_faceFinset P 1 _).mp e.property
  obtain ⟨A, B, hAB, hr⟩ := finset_subtype_pair (faceFinset P 2) (incidentFacets P e.val)
    (Finset.filter_subset _ _) (polyhedron_incident_facets_card P hfull he hd)
  refine ⟨A, B, hAB, ?_⟩
  intro F
  simpa only [incidentFacets, Finset.mem_filter, F.property, true_and] using hr F

/-- Constant values across geometric edges propagate to all vertices. -/
theorem vertexIncidence_connected (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (f : PolytopeVertex P → ZMod 2)
    (hlocal : ∀ (e : PolytopeFace P 1) (x y : PolytopeVertex P),
      x.val ∈ e.val → y.val ∈ e.val → f x = f y) :
    ∀ x y, f x = f y := by
  intro u w
  have key : ∀ x, Relation.ReflTransGen (AdiacentiVertici P) x w.val →
      ∀ hx : x ∈ P.vertices, f ⟨x, hx⟩ = f w := by
    intro x hwalk
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => intro hx; rfl
    | head hstep htail ih =>
      intro hx
      obtain ⟨hxV, hyV, e, he, hde, hxe, hye, _⟩ := hstep
      let e' : PolytopeFace P 1 := ⟨e, (mem_faceFinset P 1 e).mpr ⟨he, hde⟩⟩
      exact (hlocal e' ⟨_, hx⟩ ⟨_, hyV⟩ hxe hye).trans (ih hyV)
  exact key u.val (balinski_light P hfull u.val u.property w.val w.property) u.property

/-- Constant values across shared geometric edges propagate to all facets. -/
theorem facetIncidence_connected (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (f : PolytopeFace P 2 → ZMod 2)
    (hlocal : ∀ (e : PolytopeFace P 1) (A B : PolytopeFace P 2),
      e.val ⊆ A.val → e.val ⊆ B.val → f A = f B) :
    ∀ A B, f A = f B := by
  intro A B
  obtain ⟨hA, hdA⟩ := (mem_faceFinset P 2 _).mp A.property
  obtain ⟨hB, hdB⟩ := (mem_faceFinset P 2 _).mp B.property
  have key : ∀ X, Relation.ReflTransGen (FaccetteAdiacenti P) X B.val →
      ∀ hX : X ∈ faceFinset P 2, f ⟨X, hX⟩ = f B := by
    intro X hwalk
    induction hwalk using Relation.ReflTransGen.head_induction_on with
    | refl => intro hX; rfl
    | head hstep htail ih =>
      intro hX
      obtain ⟨⟨hY, hdY⟩, e, he, hde, heX, heY⟩ := hstep
      have hYmem := (mem_faceFinset P 2 _).mpr ⟨hY, hdY⟩
      let e' : PolytopeFace P 1 := ⟨e, (mem_faceFinset P 1 e).mpr ⟨he, hde⟩⟩
      exact (hlocal e' ⟨_, hX⟩ ⟨_, hYmem⟩ heX heY).trans (ih hYmem)
  exact key A.val (faccette_connesse P hfull hA hdA hB hdB) A.property

/-- The vertex incidence rank is V−1 for every solid convex polyhedron. -/
theorem vertexIncidence_rank (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (vertexIncidence P).rank + 1 = faceCount P 0 := by
  obtain ⟨v, hv⟩ := P.vertices_nonempty
  let : Nonempty (PolytopeVertex P) := ⟨⟨v, hv⟩⟩
  have h := incidence_rank (fun (e : PolytopeFace P 1) (v : PolytopeVertex P) => v.val ∈ e.val)
    (vertexIncidence_pair P) (vertexIncidence_connected P hfull)
  simpa [vertexIncidence, faceCount_zero] using h

/-- The facet incidence rank is F−1 for every solid convex polyhedron. -/
theorem facetIncidence_rank (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    (facetIncidence P).rank + 1 = faceCount P 2 := by
  have hdim : P.dim = 3 := hfull
  obtain ⟨F, hF, hdF⟩ := facet_exists P (by change 1 ≤ P.dim; omega)
  have hdF' : faceDim F = 2 := by change faceDim F = P.dim - 1 at hdF; omega
  let : Nonempty (PolytopeFace P 2) := ⟨⟨F, (mem_faceFinset P 2 F).mpr ⟨hF, hdF'⟩⟩⟩
  have h := incidence_rank (fun (e : PolytopeFace P 1) (F : PolytopeFace P 2) => e.val ⊆ F.val)
    (facetIncidence_pair P hfull) (facetIncidence_connected P hfull)
  simpa [facetIncidence] using h

/-- Within a geometric polygonal facet, each of its vertices meets exactly
two ambient edges contained in that facet. -/
theorem facet_vertex_edges_card (P : ConvexPolytope 3) {F : Set (E 3)}
    (hF : P.IsFace F) (hdF : faceDim F = 2) {v : E 3}
    (hv : v ∈ P.vertices) (hvF : v ∈ F) :
    ((faceFinset P 1).filter (fun e => v ∈ e ∧ e ⊆ F)).card = 2 := by
  have hdim : (facePolytope P hF).dim = 2 := by
    unfold dim
    rw [facePolytope_toSet P hF]
    exact hdF
  have hvQ : v ∈ (facePolytope P hF).vertices :=
    (mem_faceVertices P F v).mpr ⟨hv, hvF⟩
  have h := polygon_incident_edges_card (facePolytope P hF) hdim hvQ
  have heq : incidentEdges (facePolytope P hF) v =
      (faceFinset P 1).filter (fun e => v ∈ e ∧ e ⊆ F) := by
    unfold incidentEdges
    rw [facePolytope_edges P hF]
    ext e
    simp [and_comm, and_assoc]
  rwa [heq] at h

/-- The geometric boundary of a facet has zero vertex boundary over 𝔽₂.
This derives boundary-of-boundary zero directly from polygon geometry. -/
theorem incidence_boundary_squared (P : ConvexPolytope 3) :
    (vertexIncidence P).transpose * facetIncidence P = 0 := by
  ext v F
  rw [Matrix.mul_apply]
  change (∑ e : PolytopeFace P 1,
    (if v.val ∈ e.val then (1 : ZMod 2) else 0) *
      (if e.val ⊆ F.val then 1 else 0)) = 0
  have hterm (e : PolytopeFace P 1) :
      (if v.val ∈ e.val then (1 : ZMod 2) else 0) *
        (if e.val ⊆ F.val then 1 else 0) =
      if v.val ∈ e.val ∧ e.val ⊆ F.val then 1 else 0 := by
    by_cases hv : v.val ∈ e.val <;> by_cases he : e.val ⊆ F.val <;> simp [hv, he]
  simp_rw [hterm]
  rw [Finset.sum_coe_sort (faceFinset P 1)
    (fun e => if v.val ∈ e ∧ e ⊆ F.val then (1 : ZMod 2) else 0), ← Finset.sum_filter]
  have hsum : (∑ e ∈ (faceFinset P 1).filter (fun e => v.val ∈ e ∧ e ⊆ F.val),
      (1 : ZMod 2)) =
      (((faceFinset P 1).filter (fun e => v.val ∈ e ∧ e ⊆ F.val)).card : ZMod 2) := by simp
  rw [hsum]
  by_cases hvF : v.val ∈ F.val
  · obtain ⟨hF, hdF⟩ := (mem_faceFinset P 2 _).mp F.property
    rw [facet_vertex_edges_card P hF hdF v.property hvF]
    exact CharTwo.two_eq_zero
  · have hfilter : (faceFinset P 1).filter (fun e => v.val ∈ e ∧ e ⊆ F.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hinc
      exact hvF (hinc.2 hinc.1)
    rw [hfilter]
    simp

/-- A global geometric inequality for every solid convex polyhedron:
V + F ≤ E + 2. Unlike local handshake identities, this uses connectivity
of both geometric incidence graphs. -/
theorem polyhedron_vertices_facets_le_edges_add_two (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) : faceCount P 0 + faceCount P 2 ≤ faceCount P 1 + 2 := by
  have h := Matrix.rank_add_rank_le_card_of_mul_eq_zero (incidence_boundary_squared P)
  rw [Matrix.rank_transpose, card_polytopeFace] at h
  have hV := vertexIncidence_rank P hfull
  have hF := facetIncidence_rank P hfull
  omega

/-- The geometric Euler expression of every solid convex polyhedron is at
most two. Equality for arbitrary polyhedra still requires a further argument. -/
theorem polyhedron_euler_le_two (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    boundaryEuler P ≤ 2 := by
  have h := polyhedron_vertices_facets_le_edges_add_two P hfull
  unfold boundaryEuler
  omega

/-- Edge chains with zero geometric vertex boundary. -/
def edgeCycleSpace (P : ConvexPolytope 3) : Submodule (ZMod 2) (PolytopeFace P 1 → ZMod 2) :=
  LinearMap.ker (vertexIncidence P).transpose.mulVecLin

/-- Edge chains that are geometric facet boundaries. -/
def facetBoundarySpace (P : ConvexPolytope 3) : Submodule (ZMod 2) (PolytopeFace P 1 → ZMod 2) :=
  LinearMap.range (facetIncidence P).mulVecLin

/-- Every geometric facet boundary is an edge cycle. -/
theorem facetBoundarySpace_le_cycles (P : ConvexPolytope 3) :
    facetBoundarySpace P ≤ edgeCycleSpace P := by
  unfold facetBoundarySpace edgeCycleSpace
  rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul,
    incidence_boundary_squared, Matrix.mulVecLin_zero]

/-- For a solid convex polyhedron, Euler equality is equivalent to cycle filling:
every edge cycle is a sum of facet boundaries. -/
theorem polyhedron_euler_eq_two_iff_spaces (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    boundaryEuler P = 2 ↔ facetBoundarySpace P = edgeCycleSpace P := by
  have hle := facetBoundarySpace_le_cycles P
  have hnull := (vertexIncidence P).transpose.mulVecLin.finrank_range_add_finrank_ker
  change (vertexIncidence P).transpose.rank +
    Module.finrank (ZMod 2) (edgeCycleSpace P) =
    Module.finrank (ZMod 2) (PolytopeFace P 1 → ZMod 2) at hnull
  rw [Matrix.rank_transpose, Module.finrank_fintype_fun_eq_card, card_polytopeFace] at hnull
  have hV := vertexIncidence_rank P hfull
  have hF := facetIncidence_rank P hfull
  change Module.finrank (ZMod 2) (facetBoundarySpace P) + 1 = faceCount P 2 at hF
  unfold boundaryEuler
  constructor
  · intro hEuler
    apply Submodule.eq_of_le_of_finrank_le hle
    omega
  · intro heq
    have hdim := congrArg (fun S : Submodule (ZMod 2) (PolytopeFace P 1 → ZMod 2) =>
      Module.finrank (ZMod 2) S) heq
    omega

/-- An explicit cycle-filling criterion for the general Euler
formula, using only the matrices of actual exposed-face incidences. -/
theorem polyhedron_euler_eq_two_iff_cycle_filling (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) : boundaryEuler P = 2 ↔
    ∀ z : PolytopeFace P 1 → ZMod 2,
      (vertexIncidence P).transpose.mulVec z = 0 →
      ∃ c : PolytopeFace P 2 → ZMod 2, (facetIncidence P).mulVec c = z := by
  rw [polyhedron_euler_eq_two_iff_spaces P hfull]
  constructor
  · intro heq z hz
    have hcycle : z ∈ edgeCycleSpace P := hz
    rw [← heq] at hcycle
    exact hcycle
  · intro hfill
    apply le_antisymm (facetBoundarySpace_le_cycles P)
    intro z hz
    exact hfill z hz

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.incidence_rank
#check_upstream ClassicalTheorems.Progress.Euler.vertexIncidence_rank
#check_upstream ClassicalTheorems.Progress.Euler.facetIncidence_rank
#check_upstream ClassicalTheorems.Progress.Euler.incidence_boundary_squared
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_euler_le_two
#check_upstream ClassicalTheorems.Progress.Euler.polyhedron_euler_eq_two_iff_cycle_filling

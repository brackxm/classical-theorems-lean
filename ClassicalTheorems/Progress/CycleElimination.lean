/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.DescendingCycleFilling

/-! Eliminating the highest vertex of a geometric edge cycle.
The local filling from the descending vertex figure is extended to a facet
chain of the original polyhedron, without introducing vertices of greater height. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

/-- A descending edge, considered as an ambient geometric edge. -/
def descendingEdgeFace (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ)
    (e : DescendingEdge P v h) : PolytopeFace P 1 :=
  ⟨e.val.val, (mem_faceFinset P 1 _).mpr ⟨e.val.property.1, e.val.property.2.1⟩⟩

theorem descendingEdgeFace_injective (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) : Function.Injective (descendingEdgeFace P v h) := by
  intro e d heq
  have hval : e.val.val = d.val.val := congrArg (fun q : PolytopeFace P 1 => q.val) heq
  exact Subtype.ext (Subtype.ext hval)

/-- Extend a descending facet chain by zero on every other ambient facet. -/
def liftDescendingFacets (P : ConvexPolytope 3) (v : PolytopeVertex P) (h : E 3 →L[ℝ] ℝ)
    (c : DescendingFacet P v h → ZMod 2) : PolytopeFace P 2 → ZMod 2 :=
  fun F => if hF : v.val ∈ F.val ∧
    ∀ x ∈ P.vertices, x ∈ F.val → x ≠ v.val → h x < h v.val then c ⟨F, hF⟩ else 0

/-- Ambient boundary coefficients of a lifted local facet chain. -/
theorem liftDescendingFacets_boundary (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (c : DescendingFacet P v h → ZMod 2) (q : PolytopeFace P 1) :
    (facetIncidence P).mulVec (liftDescendingFacets P v h c) q =
      ∑ F : DescendingFacet P v h, (if q.val ⊆ F.val.val then (1 : ZMod 2) else 0) * c F := by
  change (∑ F : PolytopeFace P 2, (if q.val ⊆ F.val then (1 : ZMod 2) else 0) *
      liftDescendingFacets P v h c F) = _
  apply Eq.symm
  apply Fintype.sum_of_injective (fun F : DescendingFacet P v h => F.val) Subtype.val_injective
  · intro F hF
    have hnot : ¬(v.val ∈ F.val ∧
        ∀ x ∈ P.vertices, x ∈ F.val → x ≠ v.val → h x < h v.val) := by
      intro htop
      exact hF ⟨⟨F, htop⟩, rfl⟩
    simp [liftDescendingFacets, hnot]
  · intro F
    have hval : liftDescendingFacets P v h c F.val = c F := by
      dsimp only [liftDescendingFacets]
      rw [dite_eq_left F.property]
    rw [hval]

/-- On a descending edge, the lifted ambient boundary equals the local one. -/
theorem liftDescendingFacets_on_edge (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (c : DescendingFacet P v h → ZMod 2) (e : DescendingEdge P v h) :
    (facetIncidence P).mulVec (liftDescendingFacets P v h c) (descendingEdgeFace P v h e) =
      (descendingIncidence P v h).transpose.mulVec c e := by
  rw [liftDescendingFacets_boundary]
  rfl

/-- The lifted chain introduces no edge containing a different vertex at or
above the height of the vertex being eliminated. -/
theorem liftDescendingFacets_no_higher (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (c : DescendingFacet P v h → ZMod 2)
    (q : PolytopeFace P 1) (x : PolytopeVertex P) (hxq : x.val ∈ q.val)
    (hxv : x.val ≠ v.val) (hge : h v.val ≤ h x.val) :
    (facetIncidence P).mulVec (liftDescendingFacets P v h c) q = 0 := by
  rw [liftDescendingFacets_boundary]
  apply Finset.sum_eq_zero
  intro F hF
  have hnot : ¬ q.val ⊆ F.val.val := by
    intro hsub
    exact not_lt_of_ge hge (F.property.2 x.val x.property (hsub hxq) hxv)
  simp [hnot]

/-- Any nonzero edge through the highest allowed vertex is a descending edge. -/
theorem supported_incident_descending (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (hinj : Set.InjOn h (P.vertices : Set (E 3)))
    (z : PolytopeFace P 1 → ZMod 2)
    (htop : ∀ q, z q ≠ 0 → ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val ≤ h v.val)
    (q : PolytopeFace P 1) (hvq : v.val ∈ q.val) (hzq : z q ≠ 0) :
    ∃ e : DescendingEdge P v h, descendingEdgeFace P v h e = q := by
  obtain ⟨hq, hdq⟩ := (mem_faceFinset P 1 _).mp q.property
  let e : SpigoloPer P v.val := ⟨q.val, hq, hdq, hvq⟩
  have ha := SpigoloPer.altro_spec P v.val v.property e
  have hle := htop q hzq ⟨_, ha.1⟩ ha.2.1
  have hdesc : h (SpigoloPer.altro P v.val v.property e) < h v.val := by
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exact False.elim (ha.2.2.1 (hinj ha.1 v.property heq))
  exact ⟨⟨e, hdesc⟩, rfl⟩

/-- The vertex-cycle equation says that the restricted descending edge chain
has zero total coefficient, allowing the local filling theorem to apply. -/
theorem cycle_descending_sum_zero (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (hinj : Set.InjOn h (P.vertices : Set (E 3)))
    (z : PolytopeFace P 1 → ZMod 2)
    (hz : (vertexIncidence P).transpose.mulVec z = 0)
    (htop : ∀ q, z q ≠ 0 → ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val ≤ h v.val) :
    (∑ e : DescendingEdge P v h, z (descendingEdgeFace P v h e)) = 0 := by
  have hsum := Fintype.sum_of_injective (descendingEdgeFace P v h)
    (descendingEdgeFace_injective P v h) (fun e => z (descendingEdgeFace P v h e))
    (fun q : PolytopeFace P 1 => (if v.val ∈ q.val then (1 : ZMod 2) else 0) * z q) ?_ ?_
  · rw [hsum]
    exact congrFun hz v
  · intro q hq
    by_cases hvq : v.val ∈ q.val
    · have hzq : z q = 0 := by
        by_contra hn
        exact hq (supported_incident_descending P v h hinj z htop q hvq hn)
      simp [hzq]
    · simp [hvq]
  · intro e
    simp only [descendingEdgeFace, e.val.property.2.2, ite_true, one_mul]

/-- Cancel the highest vertex of any geometric edge cycle by adding actual
facet boundaries. The resulting cycle uses only vertices of smaller height. -/
theorem eliminate_highest_cycle_vertex (P : ConvexPolytope 3) (v : PolytopeVertex P)
    (h : E 3 →L[ℝ] ℝ) (hinj : Set.InjOn h (P.vertices : Set (E 3)))
    (hfill : ∀ z : DescendingEdge P v h → ZMod 2, (∑ e, z e) = 0 →
      ∃ c : DescendingFacet P v h → ZMod 2, (descendingIncidence P v h).transpose.mulVec c = z)
    (z : PolytopeFace P 1 → ZMod 2)
    (hz : (vertexIncidence P).transpose.mulVec z = 0)
    (htop : ∀ q, z q ≠ 0 → ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val ≤ h v.val) :
    ∃ c : PolytopeFace P 2 → ZMod 2,
      (vertexIncidence P).transpose.mulVec (z + (facetIncidence P).mulVec c) = 0 ∧
      ∀ q, (z + (facetIncidence P).mulVec c) q ≠ 0 →
        ∀ x : PolytopeVertex P, x.val ∈ q.val → h x.val < h v.val := by
  obtain ⟨c, hc⟩ := hfill (fun e => z (descendingEdgeFace P v h e))
    (cycle_descending_sum_zero P v h hinj z hz htop)
  let g := liftDescendingFacets P v h c
  have hmatch : ∀ q : PolytopeFace P 1, v.val ∈ q.val → (facetIncidence P).mulVec g q = z q := by
    intro q hvq
    obtain ⟨hq, hdq⟩ := (mem_faceFinset P 1 _).mp q.property
    let e : SpigoloPer P v.val := ⟨q.val, hq, hdq, hvq⟩
    by_cases hdown : h (SpigoloPer.altro P v.val v.property e) < h v.val
    · let d : DescendingEdge P v h := ⟨e, hdown⟩
      have hm := liftDescendingFacets_on_edge P v h c d
      have hval := congrFun hc d
      exact hm.trans hval
    · have ha := SpigoloPer.altro_spec P v.val v.property e
      have hg := liftDescendingFacets_no_higher P v h c q ⟨_, ha.1⟩ ha.2.1 ha.2.2.1
        (le_of_not_gt hdown)
      have hzq : z q = 0 := by
        by_contra hn
        have hle := htop q hn ⟨_, ha.1⟩ ha.2.1
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hdown hlt
        · exact ha.2.2.1 (hinj ha.1 v.property heq)
      exact hg.trans hzq.symm
  refine ⟨g, ?_, ?_⟩
  · have hb : (vertexIncidence P).transpose.mulVec ((facetIncidence P).mulVec g) = 0 := by
      rw [Matrix.mulVec_mulVec, incidence_boundary_squared]
      simp
    rw [Matrix.mulVec_add, hz, hb, add_zero]
  · intro q hq x hxq
    by_cases hxv : x.val = v.val
    · have hvq : v.val ∈ q.val := hxv ▸ hxq
      have hm := hmatch q hvq
      have hzero : (z + (facetIncidence P).mulVec g) q = 0 := by
        change z q + (facetIncidence P).mulVec g q = 0
        rw [hm, CharTwo.add_self_eq_zero]
      exact False.elim (hq hzero)
    · by_contra hnot
      have hge : h v.val ≤ h x.val := le_of_not_gt hnot
      have hzq : z q = 0 := by
        by_contra hn
        have hle := htop q hn x hxq
        exact hxv (hinj x.property v.property (le_antisymm hle hge))
      have hbq := liftDescendingFacets_no_higher P v h c q x hxq hxv hge
      apply hq
      change z q + (facetIncidence P).mulVec g q = 0
      rw [hzq, hbq, add_zero]

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.eliminate_highest_cycle_vertex

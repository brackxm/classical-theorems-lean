/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PolyhedronEuler

/-! Geometric face enumeration and Euler's formula for every solid tetrahedron.
The simplex may be any affine basis, rather than a fixed regular model.
Faces are supporting-hyperplane subsets of the actual convex hull. -/

noncomputable section
open Classical Set LeanEval.Geometry.PlatonicClassification
open ConvexPolytope
namespace ClassicalTheorems.Progress.Euler

variable {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- Barycentric coordinates expose the hull of any nonempty selection of
simplex vertices. -/
theorem basis_hull_isFace (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) (s : Finset ι) (hs : s.Nonempty) :
    P.IsFace (convexHull ℝ (b '' (s : Set ι))) := by
  let f : E n →ᵃ[ℝ] ℝ := ∑ i ∈ s, b.coord i
  let l : E n →L[ℝ] ℝ := f.linear.toContinuousLinearMap
  have hl (x : E n) : l x = f x - f 0 := by
    change f.linear x = f x - f 0
    exact congrFun f.decomp' x
  have hf (j : ι) : f (b j) = if j ∈ s then 1 else 0 := by
    have heval : ∀ t : Finset ι, (∑ i ∈ t, b.coord i) (b j) = ∑ i ∈ t, b.coord i (b j) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | @insert i t hi ih => simp [Finset.sum_insert hi, ih]
    rw [show f (b j) = ∑ i ∈ s, b.coord i (b j) from heval s]
    simp [AffineBasis.coord_apply]
  have hT : P.toSet = convexHull ℝ (range b) := by simp only [toSet, hvertices]
  have hbound : ∀ x ∈ P.toSet, l x ≤ 1 - f 0 := by
    apply le_su_toSet
    intro x hx
    rw [hvertices] at hx
    obtain ⟨j, rfl⟩ := hx
    rw [hl, hf]
    split_ifs <;> linarith
  have hconstant : ∀ x ∈ convexHull ℝ (b '' (s : Set ι)), l x = 1 - f 0 := by
    apply convexHull_min _ (convex_hyperplane (LinearMap.isLinear l.toLinearMap) (1 - f 0))
    rintro x ⟨j, hj, rfl⟩
    change l (b j) = 1 - f 0
    change j ∈ s at hj
    rw [hl, hf, ite_eq_left hj]
  refine ⟨?_, (hs.to_set.image b).convexHull⟩
  intro _
  refine ⟨l, ?_⟩
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · rw [hT]
      exact convexHull_mono (image_subset_range _ _) hx
    · intro y hy
      rw [hconstant x hx]
      exact hbound y hy
  · rintro ⟨hx, hmax⟩
    obtain ⟨i, hi⟩ := hs
    have hiT : b i ∈ P.toSet := by
      rw [hT]
      exact subset_convexHull ℝ _ (mem_range_self i)
    have hvalue : l x = 1 - f 0 := by
      have h := hmax (b i) hiT
      rw [hl, hf, ite_eq_left hi] at h
      exact le_antisymm (hbound x hx) h
    have harg := PlatoniciL3.faccia_argmax P.vertices l hx hmax
    apply convexHull_mono _ harg
    rintro y ⟨hy, hly⟩
    rw [hvertices] at hy
    obtain ⟨j, rfl⟩ := hy
    refine ⟨j, ?_, rfl⟩
    rw [hl, hf, hvalue] at hly
    by_contra hj
    change j ∉ s at hj
    rw [ite_eq_right hj] at hly
    linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Membership in a simplex subface recovers the selected vertex indices. -/
theorem basis_vertex_mem_hull_iff (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) (s : Set ι) (j : ι) :
    b j ∈ convexHull ℝ (b '' s) ↔ j ∈ s := by
  have hc : ConvexIndependent ℝ ((↑) : range b → E n) := by
    rw [← hvertices, P.vertices_eq_extremePoints]
    exact (convex_convexHull ℝ _).convexIndependent_extremePoints
  exact (b.ind.injective.convexIndependent_iff_set.mp hc).mem_convexHull_iff s j

/-- Enumerate the vertices lying in a geometric face by basis indices. -/
def basisFaceIndices (b : AffineBasis ι ℝ (E n)) (F : Set (E n)) : Finset ι :=
  Finset.univ.filter (fun i => b i ∈ F)

omit [DecidableEq ι] in
theorem basis_face_eq_hull (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) {F : Set (E n)} (hF : P.IsFace F) :
    F = convexHull ℝ (b '' (basisFaceIndices b F : Set ι)) := by
  have hfilter : ((P.vertices.filter (· ∈ F) : Finset (E n)) : Set (E n)) =
      b '' (basisFaceIndices b F : Set ι) := by
    ext x
    simp only [Finset.mem_coe, Finset.mem_filter, Set.mem_image,
      basisFaceIndices, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hxF⟩
      have hx' : x ∈ range b := by rw [← hvertices]; exact hx
      obtain ⟨i, rfl⟩ := hx'
      exact ⟨i, hxF, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hiV : b i ∈ (P.vertices : Set (E n)) := by
        rw [hvertices]; exact mem_range_self i
      exact ⟨hiV, hi⟩
  exact (face_eq_hull_vertices P hF).trans (congrArg (convexHull ℝ) hfilter)

omit [Fintype ι] [DecidableEq ι] in
/-- The dimension of a nonempty simplex subface is one less than the number
of its vertices. -/
theorem basis_hull_faceDim (b : AffineBasis ι ℝ (E n)) (s : Finset ι) (k : ℕ)
    (hcard : s.card = k + 1) : faceDim (convexHull ℝ (b '' (s : Set ι))) = k := by
  unfold faceDim
  rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
  have hd := b.ind.finrank_vectorSpan_image_finset hcard
  have himage : ((s.image (fun i => b i) : Finset (E n)) : Set (E n)) =
      b '' (s : Set ι) := Finset.coe_image
  rw [himage] at hd
  exact hd

omit [DecidableEq ι] in
theorem basis_face_indices_card (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) {F : Set (E n)} (hF : P.IsFace F) :
    (basisFaceIndices b F).card = faceDim F + 1 := by
  have heq := basis_face_eq_hull P b hvertices hF
  have hne : (basisFaceIndices b F).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hn := hF.2
    rw [heq, h] at hn
    simp at hn
  have hd := basis_hull_faceDim b (basisFaceIndices b F)
    ((basisFaceIndices b F).card - 1) (Nat.sub_add_cancel (Finset.card_pos.mpr hne)).symm
  have hdim : faceDim F = (basisFaceIndices b F).card - 1 :=
    (congrArg faceDim heq).trans hd
  have hpos := Finset.card_pos.mpr hne
  omega

/-- Every `k`-face corresponds to a `(k+1)`-element vertex subset. -/
theorem basis_facesOfDim (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) (k : ℕ) :
    facesOfDim P k = (fun s : Finset ι => convexHull ℝ (b '' (s : Set ι))) ''
      ((Finset.univ.powersetCard (k + 1) : Finset (Finset ι)) : Set (Finset ι)) := by
  ext F
  constructor
  · rintro ⟨hF, hd⟩
    refine ⟨basisFaceIndices b F, ?_, (basis_face_eq_hull P b hvertices hF).symm⟩
    simp only [Finset.mem_coe, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    rw [basis_face_indices_card P b hvertices hF, hd]
  · rintro ⟨s, hs, rfl⟩
    have hcard := (Finset.mem_powersetCard.mp hs).2
    exact ⟨basis_hull_isFace P b hvertices s (Finset.card_pos.mp (by omega)),
      basis_hull_faceDim b s k hcard⟩

/-- Actual geometric face counts for any simplex, in every dimension. -/
theorem basis_faceCount (P : ConvexPolytope n) (b : AffineBasis ι ℝ (E n))
    (hvertices : (P.vertices : Set (E n)) = range b) (k : ℕ) :
    faceCount P k = Nat.choose (Fintype.card ι) (k + 1) := by
  have hinj : Function.Injective (fun s : Finset ι => convexHull ℝ (b '' (s : Set ι))) := by
    intro s t h
    change convexHull ℝ (b '' (s : Set ι)) = convexHull ℝ (b '' (t : Set ι)) at h
    ext j
    change j ∈ (s : Set ι) ↔ j ∈ (t : Set ι)
    rw [← basis_vertex_mem_hull_iff P b hvertices s j,
      ← basis_vertex_mem_hull_iff P b hvertices t j, h]
  unfold faceCount
  rw [basis_facesOfDim P b hvertices k, hinj.injOn.ncard_image]
  simp

/-- Euler's geometric formula for every (possibly nonregular) solid tetrahedron. -/
theorem tetrahedron_euler (P : ConvexPolytope 3) (b : AffineBasis (Fin 4) ℝ (E 3))
    (hvertices : (P.vertices : Set (E 3)) = range b) : boundaryEuler P = 2 := by
  unfold boundaryEuler
  rw [basis_faceCount P b hvertices 0, basis_faceCount P b hvertices 1,
    basis_faceCount P b hvertices 2]
  norm_num [Nat.choose]

/-- A full-dimensional polytope with the minimum possible number of
vertices has an affine basis consisting of exactly those vertices. -/
theorem minimal_vertex_basis (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (hcard : P.vertices.card = n + 1) :
    ∃ b : AffineBasis {v // v ∈ P.vertices} ℝ (E n),
      (b : {v // v ∈ P.vertices} → E n) = Subtype.val := by
  let p : {v // v ∈ P.vertices} → E n := Subtype.val
  have hc : Fintype.card {v // v ∈ P.vertices} = n + 1 := by simpa using hcard
  have hrange : range p = (P.vertices : Set (E n)) := by
    ext x
    simp [p]
  have hdim : Module.finrank ℝ (vectorSpan ℝ (range p)) = n := by
    rw [hrange]
    have hd : Module.finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
    unfold toSet at hd
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan] at hd
    exact hd
  have hi : AffineIndependent ℝ p :=
    (affineIndependent_iff_finrank_vectorSpan_eq ℝ p hc).mpr hdim
  have ht : affineSpan ℝ (range p) = ⊤ := by
    apply hi.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    simpa using hc
  exact ⟨⟨p, hi, ht⟩, rfl⟩

/-- Genuine face counts for every full-dimensional simplex polytope. -/
theorem simplex_faceCount (P : ConvexPolytope n) (hfull : P.IsFullDim)
    (hcard : P.vertices.card = n + 1) (k : ℕ) :
    faceCount P k = Nat.choose (n + 1) (k + 1) := by
  obtain ⟨b, hb⟩ := minimal_vertex_basis P hfull hcard
  have hv : (P.vertices : Set (E n)) = range b := by
    rw [hb]
    ext x
    simp
  have hc : Fintype.card {v // v ∈ P.vertices} = n + 1 := by simpa using hcard
  simpa only [hc] using basis_faceCount P b hv k

/-- Euler's formula for every full-dimensional four-vertex convex polytope,
counting actual vertices, exposed edges, and exposed facets. -/
theorem four_vertex_polytope_euler (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    (_hcard : P.vertices.card = 4) : boundaryEuler P = 2 :=
  polyhedron_euler P hfull

end ClassicalTheorems.Progress.Euler
#check_upstream ClassicalTheorems.Progress.Euler.basis_hull_isFace
#check_upstream ClassicalTheorems.Progress.Euler.basis_faceCount
#check_upstream ClassicalTheorems.Progress.Euler.tetrahedron_euler
#check_upstream ClassicalTheorems.Progress.Euler.simplex_faceCount
#check_upstream ClassicalTheorems.Progress.Euler.four_vertex_polytope_euler

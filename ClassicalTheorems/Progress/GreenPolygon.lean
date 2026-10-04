/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenPiecewiseLocal
import Schoenflies.PrePolygonSep

/-! Green's theorem from certified polygon vertices. The existing Schönflies
polygon supplies the domain topology; local bridges supply its parametrization.
Collinear subdivision vertices are allowed. -/

noncomputable section
open Set MeasureTheory
namespace ClassicalTheorems.Progress.Green

/-- The raw concatenation retains its first vertex. -/
theorem rawChain_start (γ : ℕ → ℝ → ℂ) (n : ℕ) : rawChain γ n 0 = γ 0 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rawChain, joinAt, Nat.cast_nonneg] using ih

/-- The raw concatenation ends at the end of its last piece. -/
theorem rawChain_finish (γ : ℕ → ℝ → ℂ) (n : ℕ) :
    rawChain γ (n + 1) ((n : ℝ) + 1) = γ n 1 := by
  simp [rawChain, joinAt, show ¬ (n : ℝ) + 1 ≤ n by linarith]

/-- On any piece interval the raw concatenation is that original piece,
including both endpoints, when consecutive endpoints match. -/
theorem rawChain_on_piece (γ : ℕ → ℝ → ℂ) (n : ℕ)
    (hMatch : ∀ i, i + 1 < n → γ i 1 = γ (i + 1) 0)
    {i : ℕ} (hi : i < n) {t : ℝ} (ht : t ∈ Icc (i : ℝ) ((i : ℝ) + 1)) :
    rawChain γ n t = γ i (t - i) := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hin : i < n
      · have htn : t ≤ n := by
          have : (i : ℝ) + 1 ≤ n := by exact_mod_cast (show i + 1 ≤ n by omega)
          exact ht.2.trans this
        simpa only [rawChain, joinAt, ite_eq_left htn] using
          ih (fun j hj => hMatch j (by omega)) hin
      · have hie : i = n := by omega
        subst i
        have hjoin : rawChain γ n n = γ n 0 := by
          cases n with
          | zero => rfl
          | succ k => simpa only [Nat.cast_add, Nat.cast_one] using
              (rawChain_finish γ k).trans (hMatch k (by omega))
        by_cases htn : t ≤ n
        · have hte : t = n := le_antisymm htn ht.1
          simp only [hte, rawChain, joinAt, le_refl, ite_true, sub_self]
          exact hjoin
        · simp only [rawChain, joinAt, ite_eq_right htn]

/-- Read a dependency polygon vertex in complex coordinates. -/
def polygonVertex {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ZMod (m + 3)) : ℂ :=
  Complex.orthonormalBasisOneI.repr.symm (poly.vertex i)

/-- The affine unit-interval parametrization of a polygon edge. -/
def polygonEdge {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) (t : ℝ) : ℂ :=
  AffineMap.lineMap (polygonVertex poly i) (polygonVertex poly ((i : ZMod (m + 3)) + 1)) t

@[simp] theorem polygonEdge_start {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) :
    polygonEdge poly i 0 = polygonVertex poly i := by simp [polygonEdge]

@[simp] theorem polygonEdge_finish {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) :
    polygonEdge poly i 1 = polygonVertex poly ((i : ZMod (m + 3)) + 1) := by simp [polygonEdge]

/-- Polygon edges are C¹ on the whole parameter line. -/
theorem polygonEdge_contDiff {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) :
    ContDiff ℝ 1 (polygonEdge poly i) := by
  unfold polygonEdge
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  fun_prop

/-- The derivative in the polygon formula is just the difference of its vertices. -/
theorem polygonEdge_deriv {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) (t : ℝ) :
    deriv (polygonEdge poly i) t =
      polygonVertex poly ((i : ZMod (m + 3)) + 1) - polygonVertex poly i := by
  have h := ((hasDerivAt_id t).smul_const
    (polygonVertex poly ((i : ZMod (m + 3)) + 1) - polygonVertex poly i)).add_const (polygonVertex poly i)
  have hf : polygonEdge poly i = fun s : ℝ =>
      s • (polygonVertex poly ((i : ZMod (m + 3)) + 1) - polygonVertex poly i) +
        polygonVertex poly i := by
    funext s
    simp only [polygonEdge, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
  rw [hf]
  simpa only [id_eq, one_smul] using h.deriv

/-- Cyclic vertex indexing supplies every endpoint match. -/
theorem polygonEdge_match {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) :
    polygonEdge poly i 1 = polygonEdge poly (i + 1) 0 := by
  simp only [polygonEdge_finish, polygonEdge_start, Nat.cast_add, Nat.cast_one]

/-- The final polygon edge returns to its initial vertex. -/
theorem polygonEdge_closed {m : ℕ} (poly : Schoenflies.PrePolygon m) :
    polygonEdge poly (m + 2) 1 = polygonEdge poly 0 0 := by
  rw [polygonEdge_finish, polygonEdge_start]
  congr 1
  rw [← Nat.cast_one, ← Nat.cast_add]
  exact ZMod.natCast_self (m + 3)

/-- Plane coordinates recover the exact dependency edge parametrization. -/
theorem polygonEdge_repr {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) (t : ℝ) :
    Complex.orthonormalBasisOneI.repr (polygonEdge poly i t) =
      AffineMap.lineMap (poly.vertex i) (poly.vertex ((i : ZMod (m + 3)) + 1)) t := by
  simp only [polygonEdge, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
    map_add, map_smul, map_sub, polygonVertex, LinearIsometryEquiv.apply_symm_apply]

/-- A certified polygon edge has distinct endpoints. -/
theorem polygonVertex_ne_succ {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ZMod (m + 3)) :
    polygonVertex poly i ≠ polygonVertex poly (i + 1) :=
  fun h => poly.vertex_ne_succ i (Complex.orthonormalBasisOneI.repr.symm.injective h)

/-- Distinct half-open edges cannot represent the same point. This derives
parameter simplicity directly from the dependency's geometric edge condition. -/
theorem polygonEdge_injective_halfOpen {m : ℕ} (poly : Schoenflies.PrePolygon m)
    {i j : ℕ} (hi : i < m + 3) (hj : j < m + 3) {s t : ℝ}
    (hs : s ∈ Ico (0 : ℝ) 1) (ht : t ∈ Ico (0 : ℝ) 1)
    (he : polygonEdge poly i s = polygonEdge poly j t) : i = j ∧ s = t := by
  by_cases hij : i = j
  · subst j
    exact ⟨rfl, AffineMap.lineMap_injective ℝ (polygonVertex_ne_succ poly i) he⟩
  · have hij' : (i : ZMod (m + 3)) ≠ (j : ZMod (m + 3)) :=
      fun h => hij (Schoenflies.ClosedPolygon.natCast_inj hi hj h)
    have hsi : Complex.orthonormalBasisOneI.repr (polygonEdge poly i s) ∈ poly.edge i := by
      rw [polygonEdge_repr]
      exact lineMap_mem_segment ℝ _ _ ⟨hs.1, hs.2.le⟩
    have htj : Complex.orthonormalBasisOneI.repr (polygonEdge poly j t) ∈ poly.edge j := by
      rw [polygonEdge_repr]
      exact lineMap_mem_segment ℝ _ _ ⟨ht.1, ht.2.le⟩
    have hst := congrArg Complex.orthonormalBasisOneI.repr he
    have hleft (k : ℕ) (u : ℝ) (hu : u < 1)
        (hv : Complex.orthonormalBasisOneI.repr (polygonEdge poly k u) ∈
          ({poly.vertex (k : ZMod (m + 3)), poly.vertex ((k : ZMod (m + 3)) + 1)} :
            Set Schoenflies.Plane)) :
        Complex.orthonormalBasisOneI.repr (polygonEdge poly k u) = poly.vertex k := by
      simp only [mem_insert_iff, mem_singleton_iff] at hv
      rcases hv with hv | hv
      · exact hv
      · rw [polygonEdge_repr] at hv
        have hu1 := (AffineMap.lineMap_eq_right_iff.mp hv).resolve_left (poly.vertex_ne_succ k)
        exact (hu.ne hu1).elim
    have hli := hleft i s hs.2 (poly.edges_meet _ _ hij' ⟨hsi, hst.symm ▸ htj⟩)
    have hlj := hleft j t ht.2 (poly.edges_meet _ _ hij'.symm ⟨htj, hst ▸ hsi⟩)
    exact (hij' (poly.vertex_inj (hli.symm.trans (hst.trans hlj)))).elim

/-- The original concatenation of a certified polygon is simple before closing. -/
theorem polygon_rawChain_injOn {m : ℕ} (poly : Schoenflies.PrePolygon m) :
    InjOn (rawChain (polygonEdge poly) (m + 3)) (Ico (0 : ℝ) (m + 3 : ℕ)) := by
  intro s hs t ht he
  let i := ⌊s⌋₊
  let j := ⌊t⌋₊
  have hi : i < m + 3 := (Nat.floor_lt hs.1).mpr hs.2
  have hj : j < m + 3 := (Nat.floor_lt ht.1).mpr ht.2
  have hsi : s ∈ Icc (i : ℝ) ((i : ℝ) + 1) := ⟨Nat.floor_le hs.1, (Nat.lt_floor_add_one s).le⟩
  have htj : t ∈ Icc (j : ℝ) ((j : ℝ) + 1) := ⟨Nat.floor_le ht.1, (Nat.lt_floor_add_one t).le⟩
  rw [rawChain_on_piece _ _ (fun k _ => polygonEdge_match poly k) hi hsi,
    rawChain_on_piece _ _ (fun k _ => polygonEdge_match poly k) hj htj] at he
  obtain ⟨hij, hst⟩ := polygonEdge_injective_halfOpen poly hi hj
    (show s - i ∈ Ico (0 : ℝ) 1 from ⟨by linarith [hsi.1], by linarith [Nat.lt_floor_add_one s]⟩)
    (show t - j ∈ Ico (0 : ℝ) 1 from ⟨by linarith [htj.1], by linarith [Nat.lt_floor_add_one t]⟩) he
  rw [hij] at hst
  linarith

/-- The polygon edge image is exactly the dependency's geometric segment,
read in complex coordinates. -/
theorem polygonEdge_image {m : ℕ} (poly : Schoenflies.PrePolygon m) (i : ℕ) :
    polygonEdge poly i '' Icc (0 : ℝ) 1 =
      Complex.orthonormalBasisOneI.repr.symm '' poly.edge i := by
  have hf : polygonEdge poly i = Complex.orthonormalBasisOneI.repr.symm ∘
      AffineMap.lineMap (poly.vertex i) (poly.vertex ((i : ZMod (m + 3)) + 1)) := by
    funext t
    apply Complex.orthonormalBasisOneI.repr.injective
    simp only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply, polygonEdge_repr]
  rw [hf, image_comp]
  rw [Schoenflies.PrePolygon.edge, segment_eq_image_lineMap]

/-- The finite list of original unit pieces covers precisely the polygon carrier. -/
theorem polygonEdge_boundary {m : ℕ} (poly : Schoenflies.PrePolygon m) :
    (⋃ i < m + 3, polygonEdge poly i '' Icc (0 : ℝ) 1) =
      Complex.orthonormalBasisOneI.repr.symm '' poly.carrier := by
  simp_rw [polygonEdge_image]
  rw [Schoenflies.PrePolygon.carrier, image_iUnion]
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion.mpr ⟨(i : ZMod (m + 3)), hz⟩
  · intro hz
    obtain ⟨i, hz⟩ := mem_iUnion.mp hz
    refine mem_iUnion₂.mpr ⟨i.val, ZMod.val_lt i, ?_⟩
    simpa only [ZMod.natCast_zmod_val] using hz

/-- The bounded polygon interior, supplied by the dependency, in complex coordinates. -/
def polygonInterior {m : ℕ} (poly : Schoenflies.PrePolygon m) : Set ℂ :=
  Complex.orthonormalBasisOneI.repr.symm '' Schoenflies.inside poly.carrier

/-- Complex coordinates preserve the actual Lebesgue area of every certified polygon. -/
theorem polygonInterior_volume {m : ℕ} (poly : Schoenflies.PrePolygon m) :
    volume (polygonInterior poly) = volume (Schoenflies.inside poly.carrier) := by
  let e := Complex.orthonormalBasisOneI.repr
  have hImage : polygonInterior poly = e ⁻¹' Schoenflies.inside poly.carrier :=
    e.symm.toEquiv.image_eq_preimage_symm _
  rw [hImage]
  exact e.measurePreserving.measure_preimage
    poly.isSeparating_carrier.isOpen_inside.measurableSet.nullMeasurableSet

/-- Every domain and boundary hypothesis needed by Green follows from the
certified vertex geometry. No domain or frontier certificate is requested. -/
theorem polygon_geometry {m : ℕ} (poly : Schoenflies.PrePolygon m) :
    IsOpen (polygonInterior poly) ∧ Bornology.IsBounded (polygonInterior poly) ∧
      IsConnected (polygonInterior poly) ∧
        frontier (polygonInterior poly) = ⋃ i < m + 3, polygonEdge poly i '' Icc (0 : ℝ) 1 := by
  have hs := poly.isSeparating_carrier
  let e := Complex.orthonormalBasisOneI.repr.symm
  refine ⟨e.toHomeomorph.isOpenMap _ hs.isOpen_inside,
    e.lipschitz.isBounded_image hs.isBounded_inside,
    hs.isConnected_inside.image e e.continuous.continuousOn, ?_⟩
  change frontier (e '' Schoenflies.inside poly.carrier) = _
  calc
    frontier (e '' Schoenflies.inside poly.carrier) =
        e '' frontier (Schoenflies.inside poly.carrier) := (e.toHomeomorph.image_frontier _).symm
    _ = e '' poly.carrier := congrArg (image e) hs.frontier_inside
    _ = _ := (polygonEdge_boundary poly).symm

/-- Build the dependency polygon from complex vertices and geometric simplicity
data: distinct vertices and no edge crossings away from shared endpoints.
There is no parametrization, frontier or interior-topology obligation. -/
def polygonOfVertices {m : ℕ} (v : ZMod (m + 3) → ℂ) (hv : Function.Injective v)
    (hEdges : ∀ i j, i ≠ j →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆ {v i, v (i + 1)}) :
    Schoenflies.PrePolygon m := by
  let e := Complex.orthonormalBasisOneI.repr
  refine ⟨e ∘ v, e.injective.comp hv, ?_⟩
  intro i j hij z hz
  have hback (a b : ℂ) (h : z ∈ segment ℝ (e a) (e b)) :
      e.symm z ∈ segment ℝ a b := by
    have himage : e '' segment ℝ a b = segment ℝ (e a) (e b) :=
      image_segment ℝ e.toLinearEquiv.toLinearMap.toAffineMap a b
    rw [← himage] at h
    obtain ⟨x, hx, rfl⟩ := h
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hx
  have h := hEdges i j hij ⟨hback _ _ hz.1, hback _ _ hz.2⟩
  simp only [mem_insert_iff, mem_singleton_iff] at h ⊢
  rcases h with h | h
  · exact Or.inl ((e.apply_symm_apply z).symm.trans (congrArg e h))
  · exact Or.inr ((e.apply_symm_apply z).symm.trans (congrArg e h))

/-- The complex-vertex constructor preserves the supplied vertices exactly. -/
theorem polygonVertex_polygonOfVertices {m : ℕ} (v : ZMod (m + 3) → ℂ)
    (hv : Function.Injective v)
    (hEdges : ∀ i j, i ≠ j →
      segment ℝ (v i) (v (i + 1)) ∩ segment ℝ (v j) (v (j + 1)) ⊆ {v i, v (i + 1)})
    (i : ZMod (m + 3)) : polygonVertex (polygonOfVertices v hv hEdges) i = v i := by
  exact Complex.orthonormalBasisOneI.repr.symm_apply_apply (v i)

/-- The boundary integral written directly with vertex differences. -/
def polygonLineIntegral {m : ℕ} (poly : Schoenflies.PrePolygon m) (P Q : ℂ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 3), ∫ t in (0 : ℝ)..1,
    P (polygonEdge poly i t) *
        (polygonVertex poly ((i : ZMod (m + 3)) + 1) - polygonVertex poly i).re +
      Q (polygonEdge poly i t) *
        (polygonVertex poly ((i : ZMod (m + 3)) + 1) - polygonVertex poly i).im

/-- Green from certified polygon vertices. The interior, piece matching,
closedness, boundary description and parameter simplicity are all automatic.
One derived sign works for every coefficient pair. -/
theorem greens_theorem_polygon {m : ℕ} (poly : Schoenflies.PrePolygon m) (U : Set ℂ)
    (hOpen : IsOpen U) (hNeighborhood : closure (polygonInterior poly) ⊆ U) :
    ∃ orientation : Bool,
      (∀ z ∈ polygonInterior poly, (∫ t in (0 : ℝ)..(m + 3 : ℕ),
        (deriv (pausedChain (polygonEdge poly) (m + 3)) t /
          (pausedChain (polygonEdge poly) (m + 3) t - z)).im) =
            if orientation then 2 * Real.pi else -(2 * Real.pi)) ∧
      ∀ (P Q : ℂ → ℝ), ContDiffOn ℝ 1 P U → ContDiffOn ℝ 1 Q U →
        polygonLineIntegral poly P Q = (if orientation then 1 else -1) *
          ∫ z in polygonInterior poly, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨ho, hb, hc, hf⟩ := polygon_geometry poly
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_piecewise_local (polygonInterior poly) U
    (polygonEdge poly) (m + 2) (fun _ => univ) (fun _ _ => isOpen_univ)
    (fun _ _ => subset_univ _) (fun i _ => (polygonEdge_contDiff poly i).contDiffOn)
    (fun i _ => polygonEdge_match poly i) (polygonEdge_closed poly)
    (polygon_rawChain_injOn poly) ho hb hc hf hOpen hNeighborhood
  refine ⟨orientation, hw, fun P Q hP hQ => ?_⟩
  simpa only [polygonLineIntegral, polygonEdge_deriv] using hg P Q hP hQ

/-- One positive winding check gives the usual polygon Green formula.
All domain and boundary geometry is still inferred from the vertices. -/
theorem greens_theorem_polygon_of_positive_winding_at {m : ℕ} (poly : Schoenflies.PrePolygon m)
    (U : Set ℂ) (hOpen : IsOpen U) (hNeighborhood : closure (polygonInterior poly) ⊆ U)
    (z : ℂ) (hz : z ∈ polygonInterior poly)
    (hPositive : (∫ t in (0 : ℝ)..(m + 3 : ℕ),
      (deriv (pausedChain (polygonEdge poly) (m + 3)) t /
        (pausedChain (polygonEdge poly) (m + 3) t - z)).im) = 2 * Real.pi)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    polygonLineIntegral poly P Q =
      ∫ z in polygonInterior poly, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I := by
  obtain ⟨orientation, hw, hg⟩ := greens_theorem_polygon poly U hOpen hNeighborhood
  have hOrientation := orientation_eq_true_of_positive (by positivity) (hw z hz) hPositive
  simpa [hOrientation] using hg P Q hP hQ

/-- Orientation-independent Green from certified polygon vertices. -/
theorem greens_theorem_polygon_abs {m : ℕ} (poly : Schoenflies.PrePolygon m) (U : Set ℂ)
    (hOpen : IsOpen U) (hNeighborhood : closure (polygonInterior poly) ⊆ U)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |polygonLineIntegral poly P Q| =
      |∫ z in polygonInterior poly, fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| := by
  obtain ⟨orientation, _, hg⟩ := greens_theorem_polygon poly U hOpen hNeighborhood
  exact abs_eq_of_orientation_mul orientation (hg P Q hP hQ)

/-- A concrete consumer of the bridge: every noncollinear triangle supplies its
geometry through the dependency's existing vertex constructor. Only the field
neighborhood and its C¹ coefficients remain as Green hypotheses. -/
theorem greens_theorem_triangle_abs (a b c : Schoenflies.Plane)
    (hTriangle : Schoenflies.Plane.det (b - a) (c - a) ≠ 0)
    (U : Set ℂ) (hOpen : IsOpen U)
    (hNeighborhood : closure (polygonInterior (Schoenflies.triangle hTriangle).toPre) ⊆ U)
    (P Q : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    |polygonLineIntegral (Schoenflies.triangle hTriangle).toPre P Q| =
      |∫ z in polygonInterior (Schoenflies.triangle hTriangle).toPre,
        fderiv ℝ Q z (1 : ℂ) - fderiv ℝ P z Complex.I| :=
  greens_theorem_polygon_abs _ U hOpen hNeighborhood P Q hP hQ

end ClassicalTheorems.Progress.Green

#check_upstream ClassicalTheorems.Progress.Green.rawChain_start
#check_upstream ClassicalTheorems.Progress.Green.rawChain_finish
#check_upstream ClassicalTheorems.Progress.Green.rawChain_on_piece
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_contDiff
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_deriv
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_match
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_closed
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_repr
#check_upstream ClassicalTheorems.Progress.Green.polygonVertex_ne_succ
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_injective_halfOpen
#check_upstream ClassicalTheorems.Progress.Green.polygon_rawChain_injOn

#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_image
#check_upstream ClassicalTheorems.Progress.Green.polygonEdge_boundary
#check_upstream ClassicalTheorems.Progress.Green.polygon_geometry
#check_upstream ClassicalTheorems.Progress.Green.polygonOfVertices
#check_upstream ClassicalTheorems.Progress.Green.polygonVertex_polygonOfVertices
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_polygon
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_polygon_of_positive_winding_at
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_polygon_abs
#check_upstream ClassicalTheorems.Progress.Green.greens_theorem_triangle_abs

#check_upstream ClassicalTheorems.Progress.Green.polygonInterior_volume

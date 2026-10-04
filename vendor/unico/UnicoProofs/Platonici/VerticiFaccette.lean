import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.Immagini

/-!
RIGIDITÀ, GATE 6 — VERTICI E FACCETTE (18 lug 2026).

La riparazione della falla 8 del vaglio, resa corta dal nostro quadro: i
vertici di una faccetta (i vertici del suo sotto-politopo) sono per
definizione il filtro dei vertici del politopo dentro la faccetta, e come
insieme sono gli estremi della faccetta (che non dipendono dall'ambiente).
Qui: ogni vertice del politopo full-dim è vertice di una faccetta; ogni
vertice di faccetta è vertice del politopo; due politopi full-dim con le
stesse faccette hanno lo stesso toSet.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- I vertici di una faccia come insieme sono gli estremi della faccia:
non dipendono dal politopo ambiente. -/
theorem vertici_faccia_estremi (P : ConvexPolytope 3) {A : Set (E 3)}
    (hA : P.IsFace A) :
    (((facePolytope P hA).vertices : Finset (E 3)) : Set (E 3)) =
      A.extremePoints ℝ := by
  classical
  have h1 := (facePolytope P hA).vertices_eq_extremePoints
  have h2 : A = convexHull ℝ
      (((facePolytope P hA).vertices : Finset (E 3)) : Set (E 3)) :=
    face_eq_hull_vertices P hA
  rw [h1, ← h2]

/-- Ogni vertice del politopo full-dim è vertice di una faccetta. -/
theorem vertice_in_faccetta (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {x : E 3} (hx : x ∈ P.vertices) :
    ∃ (A : Set (E 3)) (hA : P.IsFace A), faceDim A = 2 ∧
      x ∈ (facePolytope P hA).vertices := by
  classical
  obtain ⟨A, B, C, hA, _, _, _, _, _⟩ := tre_faccette_al_vertice P hfull hx
  refine ⟨A, hA.1, hA.2.1, ?_⟩
  show x ∈ P.vertices.filter (· ∈ A)
  exact Finset.mem_filter.mpr ⟨hx, hA.2.2⟩

/-- Ogni vertice di una faccetta è vertice del politopo. -/
theorem vertice_di_faccetta (P : ConvexPolytope 3) {A : Set (E 3)}
    (hA : P.IsFace A) {x : E 3}
    (hx : x ∈ (facePolytope P hA).vertices) : x ∈ P.vertices := by
  classical
  have h1 : x ∈ P.vertices.filter (· ∈ A) := hx
  exact (Finset.mem_filter.mp h1).1

/-- **STESSE FACCETTE, STESSO POLITOPO**: due politopi full-dim di ℝ³ con
le stesse faccette hanno lo stesso toSet. -/
theorem toSet_eq_of_faccette_eq (P P' : ConvexPolytope 3)
    (hfull : P.IsFullDim) (hfull' : P'.IsFullDim)
    (h : ∀ A : Set (E 3),
      (P.IsFace A ∧ faceDim A = 2) ↔ (P'.IsFace A ∧ faceDim A = 2)) :
    P.toSet = P'.toSet := by
  classical
  have hvert : P.vertices = P'.vertices := by
    ext x
    constructor
    · intro hx
      obtain ⟨A, hA, hdA, hxA⟩ := vertice_in_faccetta P hfull hx
      have hA' := (h A).mp ⟨hA, hdA⟩
      -- x è estremo di A, quindi vertice del sotto-politopo di A in P'
      have hex : x ∈ A.extremePoints ℝ := by
        rw [← vertici_faccia_estremi P hA]
        exact Finset.mem_coe.mpr hxA
      have h4 : x ∈ (facePolytope P' hA'.1).vertices := by
        have h5 : x ∈ (((facePolytope P' hA'.1).vertices :
            Finset (E 3)) : Set (E 3)) := by
          rw [vertici_faccia_estremi P' hA'.1]
          exact hex
        exact Finset.mem_coe.mp h5
      exact vertice_di_faccetta P' hA'.1 h4
    · intro hx
      obtain ⟨A, hA, hdA, hxA⟩ := vertice_in_faccetta P' hfull' hx
      have hA' := (h A).mpr ⟨hA, hdA⟩
      have hex : x ∈ A.extremePoints ℝ := by
        rw [← vertici_faccia_estremi P' hA]
        exact Finset.mem_coe.mpr hxA
      have h4 : x ∈ (facePolytope P hA'.1).vertices := by
        have h5 : x ∈ (((facePolytope P hA'.1).vertices :
            Finset (E 3)) : Set (E 3)) := by
          rw [vertici_faccia_estremi P hA'.1]
          exact hex
        exact Finset.mem_coe.mp h5
      exact vertice_di_faccetta P hA'.1 h4
  show convexHull ℝ ((P.vertices : Set (E 3))) =
    convexHull ℝ ((P'.vertices : Set (E 3)))
  rw [hvert]

end LeanEval.Geometry.PlatonicClassification

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita

/-!
FASE 3A, Q2 — LA FACCIA COME SOTTO-POLITOPO (18 lug 2026).

Il motore della ricorsione per le bandiere in OGNI dimensione: una faccia f
di un politopo P, coi vertici filtrati, è essa stessa un `ConvexPolytope`
(i suoi estremi sono esattamente i vertici di P dentro f). Le facce del
sotto-politopo sono facce di P (Q0) e viceversa per restrizione del
funzionale. Con questo, l'esistenza delle bandiere scende di dimensione
in dimensione.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Una faccia di un politopo, vista come politopo (vertici filtrati). -/
noncomputable def facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : ConvexPolytope n where
  vertices := P.vertices.filter (· ∈ f)
  vertices_nonempty := by
    obtain ⟨x, hx⟩ := hf.2
    have hfe := face_eq_hull_vertices P hf
    rw [hfe] at hx
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty] at hx
    simp at hx
  vertices_eq_extremePoints := by
    have hfe := face_eq_hull_vertices P hf
    rw [← hfe, hf.1.isExtreme.extremePoints_eq]
    ext x
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hxV, hxf⟩
      refine ⟨hxf, ?_⟩
      have h1 : x ∈ (P.vertices : Set (E n)) := by exact_mod_cast hxV
      rw [P.vertices_eq_extremePoints] at h1
      exact h1
    · rintro ⟨hxf, hxe⟩
      have h1 : x ∈ (P.vertices : Set (E n)) := by
        rw [P.vertices_eq_extremePoints]
        exact hxe
      exact ⟨by exact_mod_cast h1, hxf⟩

open Classical in
theorem facePolytope_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : (facePolytope P hf).toSet = f :=
  (face_eq_hull_vertices P hf).symm

open Classical in
/-- Eredità (su): una faccia del sotto-politopo è una faccia del politopo. -/
theorem isFace_of_facePolytope (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {g : Set (E n)}
    (hg : (facePolytope P hf).IsFace g) : P.IsFace g := by
  have h1 : IsExposed ℝ f g := by
    rw [← facePolytope_toSet P hf]
    exact hg.1
  exact isFace_of_isExposed_isFace P hf h1 hg.2

open Classical in
/-- Eredità (giù): una faccia di P contenuta in f è faccia del sotto-politopo. -/
theorem facePolytope_isFace_of (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) {g : Set (E n)} (hg : P.IsFace g)
    (hsub : g ⊆ f) : (facePolytope P hf).IsFace g := by
  refine ⟨?_, hg.2⟩
  have hfT : f ⊆ P.toSet := by
    obtain ⟨lf, hlf⟩ := hf.1 hf.2
    rw [hlf]
    exact fun z hz => hz.1
  intro hne
  obtain ⟨l, hl⟩ := hg.1 hne
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀g : x₀ ∈ g := hx₀
  refine ⟨l, ?_⟩
  rw [facePolytope_toSet P hf]
  ext x
  constructor
  · intro hx
    have hxg := hx
    rw [hl] at hxg
    refine ⟨hsub hx, ?_⟩
    intro y hy
    exact hxg.2 y (hfT hy)
  · rintro ⟨hxf, hxmax⟩
    rw [hl]
    have hx₀f : x₀ ∈ f := hsub hx₀g
    have hx₀m := hxmax x₀ hx₀f
    rw [hl] at hx₀g
    refine ⟨hfT hxf, ?_⟩
    intro y hy
    calc l y ≤ l x₀ := hx₀g.2 y hy
      _ ≤ l x := hx₀m

end LeanEval.Geometry.PlatonicClassification

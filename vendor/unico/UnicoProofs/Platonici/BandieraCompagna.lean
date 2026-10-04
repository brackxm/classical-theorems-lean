import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere

/-!
FASE 3A — LA BANDIERA COMPAGNA (18 lug 2026).

Scarico completo di KG-3A1: per OGNI bandiera F di un politopo 3D esiste una
bandiera G con la stessa faccetta e spigolo diverso. Costruzione: nel
sotto-politopo Q della faccetta (dim 2) c'è un vertice w fuori dallo spigolo
(altrimenti lo spigolo conterrebbe tutti i vertici e sarebbe l'intera
faccetta); {w} è faccia (Q1), l'interpolazione (S3) dà uno spigolo f' ∋ w,
e f' ≠ F.face 1 perché w ∉ F.face 1. Corollario: `rho_orbitale_libero` —
in un politopo regolare ogni bandiera ammette una simmetria che fissa la
faccetta e muove lo spigolo, SENZA ipotesi condizionali.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- La dimensione di un singoletto è 0. -/
theorem faceDim_singleton (v : E n) : faceDim ({v} : Set (E n)) = 0 := by
  show Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E n))) = 0
  rw [vectorSpan_singleton]
  simp

/-- Una faccia diversa dal corpo lascia fuori almeno un vertice. -/
theorem exists_vertex_notMem_of_ne_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) (hne : f ≠ P.toSet) :
    ∃ w ∈ P.vertices, w ∉ f := by
  by_contra hall
  push_neg at hall
  have hconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
  have hsub : P.toSet ⊆ f := by
    show convexHull ℝ ((P.vertices : Set (E n))) ⊆ f
    apply convexHull_min ?_ hconv
    intro x hx
    exact hall x (Finset.mem_coe.mp hx)
  exact hne (Set.Subset.antisymm (face_subset_toSet P hf) hsub)

/-- **LA BANDIERA COMPAGNA**: per ogni bandiera di un politopo 3D esiste una
bandiera con la stessa faccetta e spigolo diverso. -/
theorem compagna_exists (P : ConvexPolytope 3) (F : P.Flag) :
    ∃ G : P.Flag, G.face 2 = F.face 2 ∧ G.face 1 ≠ F.face 1 := by
  classical
  have hfacet : P.IsFace (F.face 2) := F.isFace 2
  have hQtoSet : (facePolytope P hfacet).toSet = F.face 2 :=
    facePolytope_toSet P hfacet
  have hQdim :
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hfacet).toSet) = 2 := by
    rw [hQtoSet]
    exact F.dim_eq 2
  -- lo spigolo di F è una faccia del sotto-politopo della faccetta
  have hesub : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).subset
  have he : (facePolytope P hfacet).IsFace (F.face 1) :=
    facePolytope_isFace_of P hfacet (F.isFace 1) hesub
  -- lo spigolo non è tutta la faccetta (dim 1 contro 2)
  have hene : F.face 1 ≠ (facePolytope P hfacet).toSet := by
    intro h
    have h1 : faceDim (F.face 1) = 1 := F.dim_eq 1
    have h2 : faceDim (F.face 1) = 2 := by
      show Module.finrank ℝ (vectorSpan ℝ (F.face 1)) = 2
      rw [h, hQdim]
    omega
  -- un vertice della faccetta fuori dallo spigolo
  obtain ⟨w, hwV, hwe⟩ :=
    exists_vertex_notMem_of_ne_toSet (facePolytope P hfacet) he hene
  have hwF : (facePolytope P hfacet).IsFace ({w} : Set (E 3)) :=
    vertex_isFace (facePolytope P hfacet) hwV
  -- interpolazione: uno spigolo nuovo che passa per w
  have hgap : faceDim ({w} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ (facePolytope P hfacet).toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨f', hf', hwf', hf'ne⟩ := interpolazione (facePolytope P hfacet) hwF hgap
  have hf'sub : f' ⊆ F.face 2 := by
    have := face_subset_toSet (facePolytope P hfacet) hf'
    rwa [hQtoSet] at this
  have hdimf' : faceDim f' = 1 := by
    have h1 : 0 < faceDim f' := by
      have hlt := faceDim_lt_of_ssubset (facePolytope P hfacet) hwF hf' hwf'
      rw [faceDim_singleton] at hlt
      omega
    have hss : f' ⊂ (facePolytope P hfacet).toSet :=
      ⟨face_subset_toSet (facePolytope P hfacet) hf', fun hsup =>
        hf'ne (Set.Subset.antisymm
          (face_subset_toSet (facePolytope P hfacet) hf') hsup)⟩
    have h2 := faceDim_lt_of_ssubset (facePolytope P hfacet) hf'
      (toSet_isFace (facePolytope P hfacet)) hss
    have h3 : faceDim (facePolytope P hfacet).toSet = 2 := hQdim
    omega
  -- le tre inclusioni strette
  have h12 : f' ⊂ F.face 2 := by
    refine ⟨hf'sub, fun hsup => ?_⟩
    have : faceDim (F.face 2) ≤ faceDim f' :=
      le_of_eq (congrArg faceDim (Set.Subset.antisymm hsup hf'sub))
    have h4 : faceDim (F.face 2) = 2 := F.dim_eq 2
    omega
  have h02 : ({w} : Set (E 3)) ⊂ F.face 2 := hwf'.trans h12
  -- la bandiera compagna
  refine ⟨⟨fun k => if k.val = 0 then {w} else if k.val = 1 then f' else F.face 2,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact isFace_of_facePolytope P hfacet hwF
    · exact isFace_of_facePolytope P hfacet hf'
    · exact F.isFace 2
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact faceDim_singleton w
    · exact hdimf'
    · exact F.dim_eq 2
  · intro i j hij
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hij' : iv < jv := hij
    have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨ (iv = 1 ∧ jv = 2) := by
      omega
    rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · exact hwf'
    · exact h02
    · exact h12
  · rfl
  · show f' ≠ F.face 1
    intro h
    rw [h] at hwf'
    exact hwe (hwf'.subset rfl)

/-- KG-3A1, forma ratificata: con la compagna e la flag-transitività, la
simmetria che fissa la faccetta e muove lo spigolo. -/
theorem rho_orbitale (P : ConvexPolytope 3) (h : P.IsRegular)
    (F G : P.Flag) (hfacet : G.face 2 = F.face 2)
    (hedge : G.face 1 ≠ F.face 1) :
    ∃ ρ : Isom 3, P.isSymmetry ρ ∧
      ((ρ : E 3 → E 3)) '' (F.face 2) = F.face 2 ∧
      ((ρ : E 3 → E 3)) '' (F.face 1) ≠ F.face 1 := by
  obtain ⟨ρ, hρ, hface⟩ := h.2 F G
  refine ⟨ρ, hρ, (hface 2).trans hfacet, ?_⟩
  intro hfixed
  exact hedge ((hface 1).symm.trans hfixed)

/-- **KG-3A1 SCARICATO**: in un politopo 3D regolare, OGNI bandiera ammette
una simmetria che fissa la faccetta e muove lo spigolo. Nessuna ipotesi
condizionale residua. -/
theorem rho_orbitale_libero (P : ConvexPolytope 3) (h : P.IsRegular)
    (F : P.Flag) :
    ∃ ρ : Isom 3, P.isSymmetry ρ ∧
      ((ρ : E 3 → E 3)) '' (F.face 2) = F.face 2 ∧
      ((ρ : E 3 → E 3)) '' (F.face 1) ≠ F.face 1 := by
  obtain ⟨G, hG2, hG1⟩ := compagna_exists P F
  exact rho_orbitale P h F G hG2 hG1

end LeanEval.Geometry.PlatonicClassification

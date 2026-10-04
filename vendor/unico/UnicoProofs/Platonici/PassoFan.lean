import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SecondoSpigolo
import UnicoProofs.Platonici.SecondaFaccetta
import UnicoProofs.Platonici.BandieraVertice

/-!
FASE 3A, F6 — IL PASSO DEL FAN (18 lug 2026).

Da una bandiera F al vertice v, le bandiere ausiliarie del gemello KG-3A2:
δ := il secondo spigolo della faccetta di F in v (diverso da F.face 1),
A₂ := la seconda faccetta per δ (diversa dalla faccetta di F). Allora
L := (v, δ, faccetta di F) e G = R := (v, δ, A₂) soddisfano esattamente le
ipotesi di posizione del kill-gate: L.face 2 = F.face 2, R.face 2 = G.face 2,
L.face 1 = R.face 1, e in più G avanza davvero (faccetta diversa, e lo
spigolo condiviso è diverso da quello di F).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Assemblaggio di una bandiera (v, δ, A) da pezzi con le giuste dimensioni. -/
theorem bandiera_di_pezzi (P : ConvexPolytope 3) {v : E 3}
    (hvface : P.IsFace ({v} : Set (E 3)))
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1) (hvδ : v ∈ δ)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hδA : δ ⊆ A) :
    ∃ F : P.Flag, F.face 0 = {v} ∧ F.face 1 = δ ∧ F.face 2 = A := by
  have h01 : ({v} : Set (E 3)) ⊂ δ := by
    refine ⟨Set.singleton_subset_iff.mpr hvδ, fun hsup => ?_⟩
    have h1 : δ = {v} := Set.Subset.antisymm hsup
      (Set.singleton_subset_iff.mpr hvδ)
    rw [h1] at hdδ
    rw [faceDim_singleton] at hdδ
    omega
  have h12 : δ ⊂ A := by
    refine ⟨hδA, fun hsup => ?_⟩
    have h1 : δ = A := Set.Subset.antisymm hδA hsup
    rw [h1, hdA] at hdδ
    omega
  refine ⟨⟨fun k => if k.val = 0 then {v} else if k.val = 1 then δ else A,
    ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact hvface
    · exact hδ
    · exact hA
  · intro k
    rcases k with ⟨kv, hk⟩
    interval_cases kv
    · exact faceDim_singleton v
    · exact hdδ
    · exact hdA
  · intro i j hij
    rcases i with ⟨iv, hi⟩
    rcases j with ⟨jv, hj⟩
    have hij' : iv < jv := hij
    have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨
        (iv = 1 ∧ jv = 2) := by omega
    rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
    · exact h01
    · exact h01.trans h12
    · exact h12

/-- **IL PASSO DEL FAN**: da una bandiera in v, le bandiere G, L, R del
kill-gate, con G che avanza davvero. -/
theorem passo_del_fan (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) (F : P.Flag) (hF0 : F.face 0 = {v}) :
    ∃ G L R : P.Flag, G.face 0 = {v} ∧ L.face 0 = {v} ∧
      L.face 2 = F.face 2 ∧ R.face 2 = G.face 2 ∧ L.face 1 = R.face 1 ∧
      G.face 2 ≠ F.face 2 ∧ L.face 1 ≠ F.face 1 ∧ G.face 1 = L.face 1 := by
  classical
  have hvface : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hv
  -- la faccetta e lo spigolo di F, con v dentro
  have hA₁ : P.IsFace (F.face 2) := F.isFace 2
  have hdA₁ : faceDim (F.face 2) = 2 := F.dim_eq 2
  have hε₁ : P.IsFace (F.face 1) := F.isFace 1
  have hdε₁ : faceDim (F.face 1) = 1 := F.dim_eq 1
  have hv1 : v ∈ F.face 1 := (F.strict_mono 0 1 (by decide)).subset
    (hF0 ▸ rfl)
  have hv2 : v ∈ F.face 2 := (F.strict_mono 1 2 (by decide)).subset hv1
  have hε₁A₁ : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).subset
  -- il poligono della faccetta
  have hQdim : Module.finrank ℝ
      (vectorSpan ℝ (facePolytope P hA₁).toSet) = 2 := by
    rw [facePolytope_toSet P hA₁]
    exact hdA₁
  have hvQ : v ∈ (facePolytope P hA₁).vertices := by
    show v ∈ P.vertices.filter (· ∈ F.face 2)
    exact Finset.mem_filter.mpr ⟨hv, hv2⟩
  have hε₁Q : (facePolytope P hA₁).IsFace (F.face 1) :=
    facePolytope_isFace_of P hA₁ hε₁ hε₁A₁
  -- il secondo spigolo della faccetta in v
  obtain ⟨δ, hδQ, hdδ, hvδ, hδne⟩ := secondo_spigolo (facePolytope P hA₁)
    hQdim hvQ hε₁Q hdε₁ hv1
  have hδ : P.IsFace δ := isFace_of_facePolytope P hA₁ hδQ
  have hδA₁ : δ ⊆ F.face 2 := by
    have h1 := face_subset_toSet (facePolytope P hA₁) hδQ
    rwa [facePolytope_toSet P hA₁] at h1
  -- la seconda faccetta per δ
  obtain ⟨A₂, hA₂, hdA₂, hδA₂, hA₂ne⟩ := seconda_faccetta P hfull hδ hdδ
    hA₁ hdA₁ hδA₁
  -- le bandiere
  obtain ⟨L, hL0, hL1, hL2⟩ := bandiera_di_pezzi P hvface hδ hdδ hvδ
    hA₁ hdA₁ hδA₁
  obtain ⟨G, hG0, hG1, hG2⟩ := bandiera_di_pezzi P hvface hδ hdδ hvδ
    hA₂ hdA₂ hδA₂
  refine ⟨G, L, G, hG0, hL0, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hL2]
  · rw [hL1, hG1]
  · rw [hG2]
    exact hA₂ne
  · rw [hL1]
    exact hδne
  · rw [hL1, hG1]

end LeanEval.Geometry.PlatonicClassification

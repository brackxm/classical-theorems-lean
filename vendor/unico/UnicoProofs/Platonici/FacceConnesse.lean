/- Modified for the ClassicalTheorems project by Codex on 2026-10-02:
   compatibility updates for Lean 4.34.0 and the pinned mathlib revision. -/

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ConnessioneVentaglio
import UnicoProofs.Platonici.VerticiFaccette

/-!
RIGIDITÀ — CONNETTIVITÀ GLOBALE DELLE FACCETTE (18-19 lug 2026).

La riparazione della falla 10 (il vaglio aveva ricevuto per certificata la
connettività globale, che invece era solo quella del ventaglio locale).
Qui il grafo globale delle faccette (adiacenza = spigolo condiviso) è
connesso, CONDIZIONATAMENTE alla connettività del grafo dei vertici
(Balinski-light, in arrivo con il cono del vertice): un cammino di vertici
si solleva a un cammino di faccette usando il ventaglio a ogni tappa e la
stella di ogni spigolo attraversato. In coda, l'induzione per coincidenza
in forma astratta: un insieme chiuso per adiacenza che contiene un punto
contiene tutto ciò che il cammino raggiunge.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Adiacenza fra vertici del politopo: estremi di uno stesso spigolo. -/
def AdiacentiVertici (P : ConvexPolytope 3) (u w : E 3) : Prop :=
  u ∈ P.vertices ∧ w ∈ P.vertices ∧
    ∃ δ : Set (E 3), P.IsFace δ ∧ faceDim δ = 1 ∧ u ∈ δ ∧ w ∈ δ ∧ u ≠ w

/-- Adiacenza globale fra faccette: la meta è una faccetta e le due
condividono uno spigolo. -/
def FaccetteAdiacenti (P : ConvexPolytope 3) (A B : Set (E 3)) : Prop :=
  (P.IsFace B ∧ faceDim B = 2) ∧
    ∃ δ : Set (E 3), P.IsFace δ ∧ faceDim δ = 1 ∧ δ ⊆ A ∧ δ ⊆ B

/-- L'induzione per coincidenza, in astratto: un insieme chiuso per la
relazione che contiene la base contiene ogni punto raggiungibile. -/
theorem induzione_coincidenza {α : Type*} {r : α → α → Prop} {S : Set α}
    (hchiuso : ∀ a ∈ S, ∀ b, r a b → b ∈ S) {a b : α}
    (ha : a ∈ S) (h : Relation.ReflTransGen r a b) : b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact hchiuso _ ih _ hstep

/-- Ogni faccia ha un vertice del politopo. -/
theorem faccetta_ha_vertice (P : ConvexPolytope 3) {A : Set (E 3)}
    (hA : P.IsFace A) : ∃ u, u ∈ P.vertices ∧ u ∈ A := by
  classical
  obtain ⟨u, hu⟩ := (facePolytope P hA).vertices_nonempty
  have h1 : u ∈ P.vertices.filter (· ∈ A) := hu
  have h2 := Finset.mem_filter.mp h1
  exact ⟨u, h2.1, h2.2⟩

/-- Il ventaglio attorno a un vertice, letto nell'adiacenza globale. -/
theorem ventaglio_globale (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices)
    {A B : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (hB : P.IsFace B) (hdB : faceDim B = 2) (hvB : v ∈ B) :
    Relation.ReflTransGen (FaccetteAdiacenti P) A B := by
  have h := ventaglio_connesso P hfull hv hA hdA hvA hB hdB hvB
  refine Relation.ReflTransGen.mono ?_ _ _ h
  rintro X Y ⟨⟨hY, hdY, _⟩, δ, hδ, hdδ, _, hδX, hδY⟩
  exact ⟨⟨hY, hdY⟩, δ, hδ, hdδ, hδX, hδY⟩

/-- **CONNETTIVITÀ GLOBALE DELLE FACCETTE**, condizionale alla
connettività del grafo dei vertici: un cammino di vertici si solleva a un
cammino di faccette (stella dello spigolo a ogni passo, ventaglio a ogni
tappa). -/
theorem faccette_connesse_globale (P : ConvexPolytope 3)
    (hfull : P.IsFullDim)
    (hbal : ∀ u ∈ P.vertices, ∀ w ∈ P.vertices,
      Relation.ReflTransGen (AdiacentiVertici P) u w)
    {A B : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2) :
    Relation.ReflTransGen (FaccetteAdiacenti P) A B := by
  classical
  obtain ⟨u, hu, huA⟩ := faccetta_ha_vertice P hA
  obtain ⟨w, hw, hwB⟩ := faccetta_ha_vertice P hB
  have key : ∀ x, Relation.ReflTransGen (AdiacentiVertici P) x w →
      ∀ X : Set (E 3), P.IsFace X → faceDim X = 2 → x ∈ X →
      x ∈ P.vertices →
      Relation.ReflTransGen (FaccetteAdiacenti P) X B := by
    intro x hx
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro X hX hdX hwX hxv
      exact ventaglio_globale P hfull hxv hX hdX hwX hB hdB hwB
    | head hstep htail ih =>
      intro X hX hdX hxX hxv
      obtain ⟨hxv', hyv, δ, hδ, hdδ, hxδ, hyδ, hne⟩ := hstep
      obtain ⟨D⟩ := stella_spigolo_esiste P hfull hxv' ⟨δ, hδ, hdδ, hxδ⟩
      have h1 : Relation.ReflTransGen (FaccetteAdiacenti P) X D.A :=
        ventaglio_globale P hfull hxv' hX hdX hxX D.hA D.hdA (D.heA hxδ)
      have h2 : Relation.ReflTransGen (FaccetteAdiacenti P) D.A B :=
        ih D.A D.hA D.hdA (D.heA hyδ) hyv
      exact h1.trans h2
  exact key u (hbal u hu w hw) A hA hdA huA hu

end LeanEval.Geometry.PlatonicClassification

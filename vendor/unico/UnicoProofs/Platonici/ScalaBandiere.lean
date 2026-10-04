import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione

/-!
FASE 3A, Q3-S4 — LA SCALA: facet_exists e la catena delle facce (18 lug 2026).

Con l'interpolazione (S3) e la dimensione stretta (S3b): da un vertice si sale
di faccia in faccia fino alla faccetta (dim esattamente d−1); con il
sotto-politopo (Q2) si scende ricorsivamente costruendo la catena completa
di facce di dimensioni esatte 0,1,…,d−1. LE BANDIERE ESISTONO, in ogni
dimensione.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Il corpo è una faccia di sé stesso (esposto dal funzionale nullo). -/
theorem toSet_isFace (P : ConvexPolytope n) : P.IsFace P.toSet := by
  constructor
  · intro _
    refine ⟨0, ?_⟩
    ext x
    simp
  · obtain ⟨v, hv⟩ := P.vertices_nonempty
    exact ⟨v, subset_convexHull ℝ _ (by exact_mod_cast hv)⟩

/-- Ogni faccia sta nel corpo. -/
theorem face_subset_toSet (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) : f ⊆ P.toSet := by
  obtain ⟨l, hl⟩ := hf.1 hf.2
  rw [hl]
  exact fun z hz => hz.1

/-- S4a: ogni politopo di dimensione ≥ 1 ha una faccetta (dim esattamente d−1). -/
theorem facet_exists (P : ConvexPolytope n)
    (hd : 1 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet)) :
    ∃ f : Set (E n), P.IsFace f ∧
      faceDim f = Module.finrank ℝ (vectorSpan ℝ P.toSet) - 1 := by
  classical
  set d : ℕ := Module.finrank ℝ (vectorSpan ℝ P.toSet) with hdd
  suffices H : ∀ k : ℕ, ∀ f : Set (E n), P.IsFace f →
      d - 1 - faceDim f ≤ k → faceDim f ≤ d - 1 →
      ∃ g : Set (E n), P.IsFace g ∧ faceDim g = d - 1 by
    obtain ⟨v, hv⟩ := P.vertices_nonempty
    have h0 : P.IsFace ({v} : Set (E n)) := vertex_isFace P hv
    have hdim0 : faceDim ({v} : Set (E n)) = 0 := by
      show Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E n))) = 0
      rw [vectorSpan_singleton]
      simp
    exact H (d - 1) {v} h0 (by omega) (by omega)
  intro k
  induction k with
  | zero =>
    intro f hf hk hle
    exact ⟨f, hf, by omega⟩
  | succ m ih =>
    intro f hf hk hle
    by_cases heq : faceDim f = d - 1
    · exact ⟨f, hf, heq⟩
    · have hgap : faceDim f + 2 ≤ d := by omega
      obtain ⟨f', hf', hsub, hne⟩ := interpolazione P hf hgap
      have hlt : faceDim f < faceDim f' := faceDim_lt_of_ssubset P hf hf' hsub
      have hlt2 : faceDim f' < d := by
        have hss : f' ⊂ P.toSet := ⟨face_subset_toSet P hf', hne ∘ (fun h =>
          Set.Subset.antisymm (face_subset_toSet P hf') h)⟩
        have := faceDim_lt_of_ssubset P hf' (toSet_isFace P) hss
        exact this
      exact ih f' hf' (by omega) (by omega)

/-- S4b: la catena completa — per ogni politopo, una successione di facce di
dimensioni esatte 0,…,d−1, strettamente crescente. -/
theorem chain_exists (P : ConvexPolytope n) :
    ∀ d : ℕ, Module.finrank ℝ (vectorSpan ℝ P.toSet) = d →
    ∃ c : ℕ → Set (E n),
      (∀ k, k < d → P.IsFace (c k) ∧ faceDim (c k) = k) ∧
      (∀ j k, j < k → k < d → c j ⊂ c k) := by
  classical
  intro d
  induction d generalizing P with
  | zero =>
    intro _
    exact ⟨fun _ => ∅, fun k hk => absurd hk (by omega),
      fun j k hjk hk => absurd hk (by omega)⟩
  | succ m ih =>
    intro hdim
    -- la faccetta di dimensione m
    have hd1 : 1 ≤ Module.finrank ℝ (vectorSpan ℝ P.toSet) := by omega
    obtain ⟨f, hf, hfdim⟩ := facet_exists P hd1
    rw [hdim] at hfdim
    simp only [Nat.add_sub_cancel] at hfdim
    -- ricorsione nel sotto-politopo
    have hsubdim : Module.finrank ℝ (vectorSpan ℝ (facePolytope P hf).toSet) = m := by
      rw [facePolytope_toSet P hf]
      exact hfdim
    obtain ⟨c', hc'1, hc'2⟩ := ih (facePolytope P hf) hsubdim
    refine ⟨fun k => if k = m then f else c' k, ?_, ?_⟩
    · intro k hk
      by_cases hkm : k = m
      · subst hkm
        simp only [if_pos rfl]
        exact ⟨hf, hfdim⟩
      · have hklt : k < m := by omega
        simp only [if_neg hkm]
        obtain ⟨h1, h2⟩ := hc'1 k hklt
        exact ⟨isFace_of_facePolytope P hf h1, h2⟩
    · intro j k hjk hk
      by_cases hkm : k = m
      · subst hkm
        have hjm : j ≠ k := by omega
        have hjlt : j < k := hjk
        simp only [if_pos rfl, if_neg hjm]
        obtain ⟨h1, h2⟩ := hc'1 j hjlt
        constructor
        · have hsub1 : c' j ⊆ (facePolytope P hf).toSet :=
            face_subset_toSet (facePolytope P hf) h1
          rwa [facePolytope_toSet P hf] at hsub1
        · intro hcontra
          have hsub1 : c' j ⊆ (facePolytope P hf).toSet :=
            face_subset_toSet (facePolytope P hf) h1
          rw [facePolytope_toSet P hf] at hsub1
          have hfeq : c' j = f := Set.Subset.antisymm hsub1 hcontra
          have := h2
          rw [hfeq] at this
          omega
      · have hklt : k < m := by omega
        have hjm : j ≠ m := by omega
        simp only [if_neg hkm, if_neg hjm]
        exact hc'2 j k hjk hklt

/-- S4: LE BANDIERE ESISTONO — ogni politopo full-dimensionale ha una Flag. -/
theorem flag_exists (P : ConvexPolytope n) (hfull : P.IsFullDim) :
    Nonempty (P.Flag) := by
  classical
  have hdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = n := hfull
  obtain ⟨c, hc1, hc2⟩ := chain_exists P n hdim
  refine ⟨⟨fun k => c k, ?_, ?_, ?_⟩⟩
  · intro k
    exact (hc1 k k.isLt).1
  · intro k
    exact (hc1 k k.isLt).2
  · intro i j hij
    exact hc2 i j hij j.isLt

end LeanEval.Geometry.PlatonicClassification

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna

/-!
FASE 3A — LA BANDIERA AL VERTICE E LA FINITEZZA DELLE FACCE (18 lug 2026).

Tre attrezzi per il fan: (1) una faccia di dimensione 0 è un singoletto;
(2) per OGNI vertice di un politopo full-dim di ℝ³ esiste una bandiera che
parte da quel vertice (con la scala: interpolazione dal singoletto, e nel
caso il salto arrivi subito alla faccetta si ridiscende nel sotto-politopo);
(3) le facce di un politopo sono finite (ogni faccia è l'hull dei propri
vertici, e i sottoinsiemi dei vertici sono finiti).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione 0 è un singoletto. -/
theorem faccia_dim0_singoletto {f : Set (E n)} (hne : f.Nonempty)
    (hd : faceDim f = 0) : ∃ x, f = {x} := by
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    have hmem : y - x ∈ vectorSpan ℝ f := vsub_mem_vectorSpan ℝ hy hx
    have hbot : vectorSpan ℝ f = ⊥ := by
      have hd' : Module.finrank ℝ (vectorSpan ℝ f) = 0 := hd
      exact Submodule.finrank_eq_zero.mp hd'
    rw [hbot] at hmem
    have : y - x = 0 := hmem
    have : y = x := by
      have h1 := congrArg (fun q => q + x) this
      simpa using h1
    exact this ▸ rfl
  · intro hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hx

/-- Per ogni vertice di un politopo full-dim di ℝ³ c'è una bandiera che
parte da quel vertice. -/
theorem bandiera_al_vertice (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ F : P.Flag, F.face 0 = {v} := by
  classical
  have hvface : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hv
  have hd0 : faceDim ({v} : Set (E 3)) = 0 := faceDim_singleton v
  have hgap0 : faceDim ({v} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    rw [hd0, h1]
    omega
  obtain ⟨g, hg, hvg, hgne⟩ := interpolazione P hvface hgap0
  have hdg : 0 < faceDim g := by
    have h1 := faceDim_lt_of_ssubset P hvface hg hvg
    rw [hd0] at h1
    omega
  have hdg3 : faceDim g < 3 := by
    have hss : g ⊂ P.toSet :=
      ⟨face_subset_toSet P hg, fun hsup => hgne
        (Set.Subset.antisymm (face_subset_toSet P hg) hsup)⟩
    have h1 := faceDim_lt_of_ssubset P hg (toSet_isFace P) hss
    have h2 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
    have h3 : Module.finrank ℝ (vectorSpan ℝ g) <
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := h1
    have h4 : faceDim g = Module.finrank ℝ (vectorSpan ℝ g) := rfl
    omega
  have hvmemg : v ∈ g := hvg.subset rfl
  -- due casi: g è uno spigolo o una faccetta
  rcases Nat.lt_or_ge (faceDim g) 2 with hcase | hcase
  · -- g spigolo: lo si estende a faccetta
    have hdg1 : faceDim g = 1 := by omega
    have hgapg : faceDim g + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      rw [hdg1, h1]
    obtain ⟨A, hA, hgA, hAne⟩ := interpolazione P hg hgapg
    have hdA : faceDim A = 2 := by
      have h1 := faceDim_lt_of_ssubset P hg hA hgA
      have hss : A ⊂ P.toSet :=
        ⟨face_subset_toSet P hA, fun hsup => hAne
          (Set.Subset.antisymm (face_subset_toSet P hA) hsup)⟩
      have h2 := faceDim_lt_of_ssubset P hA (toSet_isFace P) hss
      have h3 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      have h4 : faceDim A = Module.finrank ℝ (vectorSpan ℝ A) := rfl
      have h5 : Module.finrank ℝ (vectorSpan ℝ A) <
          Module.finrank ℝ (vectorSpan ℝ P.toSet) := h2
      omega
    refine ⟨⟨fun k => if k.val = 0 then {v} else if k.val = 1 then g else A,
      ?_, ?_, ?_⟩, rfl⟩
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hvface
      · exact hg
      · exact hA
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hd0
      · exact hdg1
      · exact hdA
    · intro i j hij
      rcases i with ⟨iv, hi⟩
      rcases j with ⟨jv, hj⟩
      have hij' : iv < jv := hij
      have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨
          (iv = 1 ∧ jv = 2) := by omega
      rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
      · exact hvg
      · exact hvg.trans hgA
      · exact hgA
  · -- g faccetta: si ridiscende nel sotto-politopo per trovare lo spigolo
    have hdg2 : faceDim g = 2 := by omega
    have hQdim : Module.finrank ℝ
        (vectorSpan ℝ (facePolytope P hg).toSet) = 2 := by
      rw [facePolytope_toSet P hg]
      exact hdg2
    have hvQ : (facePolytope P hg).IsFace ({v} : Set (E 3)) :=
      facePolytope_isFace_of P hg hvface (Set.singleton_subset_iff.mpr hvmemg)
    have hgapQ : faceDim ({v} : Set (E 3)) + 2 ≤
        Module.finrank ℝ (vectorSpan ℝ (facePolytope P hg).toSet) := by
      rw [hd0, hQdim]
    obtain ⟨e, he, hve, hene⟩ := interpolazione (facePolytope P hg) hvQ hgapQ
    have hdE : faceDim e = 1 := by
      have h1 := faceDim_lt_of_ssubset (facePolytope P hg) hvQ he hve
      rw [hd0] at h1
      have hss : e ⊂ (facePolytope P hg).toSet :=
        ⟨face_subset_toSet (facePolytope P hg) he, fun hsup => hene
          (Set.Subset.antisymm
            (face_subset_toSet (facePolytope P hg) he) hsup)⟩
      have h2 := faceDim_lt_of_ssubset (facePolytope P hg) he
        (toSet_isFace (facePolytope P hg)) hss
      have h3 : faceDim (facePolytope P hg).toSet = 2 := hQdim
      omega
    have heP : P.IsFace e := isFace_of_facePolytope P hg he
    have hesub : e ⊆ g := by
      have h1 := face_subset_toSet (facePolytope P hg) he
      rwa [facePolytope_toSet P hg] at h1
    have heg : e ⊂ g := by
      refine ⟨hesub, fun hsup => ?_⟩
      have h1 : e = g := Set.Subset.antisymm hesub hsup
      rw [h1] at hdE
      omega
    refine ⟨⟨fun k => if k.val = 0 then {v} else if k.val = 1 then e else g,
      ?_, ?_, ?_⟩, rfl⟩
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hvface
      · exact heP
      · exact hg
    · intro k
      rcases k with ⟨kv, hk⟩
      interval_cases kv
      · exact hd0
      · exact hdE
      · exact hdg2
    · intro i j hij
      rcases i with ⟨iv, hi⟩
      rcases j with ⟨jv, hj⟩
      have hij' : iv < jv := hij
      have hcasi : (iv = 0 ∧ jv = 1) ∨ (iv = 0 ∧ jv = 2) ∨
          (iv = 1 ∧ jv = 2) := by omega
      rcases hcasi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 <;> subst h2
      · exact hve
      · exact hvg
      · exact heg

/-- Le facce di un politopo sono finite. -/
theorem facce_finite (P : ConvexPolytope n) :
    {f : Set (E n) | P.IsFace f}.Finite := by
  classical
  apply Set.Finite.of_finite_image (f := fun f => P.vertices.filter (· ∈ f))
  · apply Set.Finite.subset (Set.finite_range
      (fun s : {s : Finset (E n) // s ⊆ P.vertices} => (s : Finset (E n))))
    rintro _ ⟨f, _, rfl⟩
    exact ⟨⟨P.vertices.filter (· ∈ f), Finset.filter_subset _ _⟩, rfl⟩
  · intro f hf g hg heq
    have h1 : f = convexHull ℝ
        ((P.vertices.filter (· ∈ f) : Finset (E n)) : Set (E n)) :=
      face_eq_hull_vertices P hf
    have h2 : g = convexHull ℝ
        ((P.vertices.filter (· ∈ g) : Finset (E n)) : Set (E n)) :=
      face_eq_hull_vertices P hg
    have heq' : P.vertices.filter (· ∈ f) = P.vertices.filter (· ∈ g) := heq
    rw [h1, h2, heq']

end LeanEval.Geometry.PlatonicClassification

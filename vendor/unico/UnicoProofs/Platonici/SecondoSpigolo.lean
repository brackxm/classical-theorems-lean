import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.Interpolazione

/-!
FASE 3A, F3 — IL SECONDO SPIGOLO (18 lug 2026).

In un poligono (politopo di rango 2), ogni vertice con un spigolo e₁ ha un
secondo spigolo e₂ ≠ e₁. Perno esplicito: scelto w ≠ 0 nello span del
poligono ortogonale alla direzione u₁ − v di e₁, si ruota l'espositore del
vertice: ψ = l_v + t*·⟪w,·⟫ col t* critico (minimo dei rapporti sui vertici
dal lato buono di w). L'argmax di ψ è una faccia per definizione; contiene v
e il vertice critico u*, quindi ha rango ≥ 1; e u₁ NON può starci (ψ(u₁) =
ψ(v) forzerebbe l_v(u₁) = l_v(v), cioè u₁ = v): questo esclude in un colpo
solo sia F = e₁ sia F = corpo. Dunque F è uno spigolo per v diverso da e₁.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Nello span di rango ≥ 2 c'è un vettore non nullo ortogonale a una
direzione data. -/
theorem esiste_ortogonale_nello_span {W : Submodule ℝ (E n)}
    (hW : 2 ≤ Module.finrank ℝ W) (d : E n) :
    ∃ w : E n, w ∈ W ∧ w ≠ 0 ∧ ⟪w, d⟫ = 0 := by
  classical
  set f : W →ₗ[ℝ] ℝ := (innerSL ℝ d).toLinearMap.comp W.subtype with hf
  have hrange : Module.finrank ℝ (LinearMap.range f) ≤ 1 := by
    have h1 : Module.finrank ℝ (LinearMap.range f) ≤ Module.finrank ℝ ℝ :=
      Submodule.finrank_le _
    simpa using h1
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  have hker : 1 ≤ Module.finrank ℝ (LinearMap.ker f) := by omega
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h] at hker
    simp [finrank_bot] at hker
  obtain ⟨w, hwker, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨(w : E n), w.2, ?_, ?_⟩
  · intro h
    apply hwne
    exact Subtype.ext h
  · have h1 : f w = 0 := hwker
    have h2 : ⟪d, (w : E n)⟫ = 0 := h1
    rw [real_inner_comm] at h2
    exact h2

/-- **IL SECONDO SPIGOLO**: in un poligono ogni vertice con uno spigolo ne
ha un secondo, diverso. -/
theorem secondo_spigolo (Q : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2)
    {v : E n} (hv : v ∈ Q.vertices)
    {e₁ : Set (E n)} (he₁ : Q.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (hve₁ : v ∈ e₁) :
    ∃ e₂ : Set (E n), Q.IsFace e₂ ∧ faceDim e₂ = 1 ∧ v ∈ e₂ ∧ e₂ ≠ e₁ := by
  classical
  -- l'espositore del vertice
  obtain ⟨l, hl⟩ := (vertex_isFace Q hv).1 (Set.singleton_nonempty v)
  have hvT : v ∈ Q.toSet := by
    have : v ∈ ({v} : Set (E n)) := rfl
    rw [hl] at this
    exact this.1
  have hlmax : ∀ y ∈ Q.toSet, l y ≤ l v := by
    have : v ∈ ({v} : Set (E n)) := rfl
    rw [hl] at this
    exact this.2
  have hlchar : ∀ q ∈ Q.toSet, l q = l v → q = v := by
    intro q hq hlq
    have : q ∈ ({v} : Set (E n)) := by
      rw [hl]
      exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
    exact this
  -- il secondo punto di e₁ e la sua direzione
  obtain ⟨u₁, hu₁e, hu₁v⟩ := faccia_ha_secondo_punto hde₁ (v := v)
  have hu₁T : u₁ ∈ Q.toSet := face_subset_toSet Q he₁ hu₁e
  -- u₁ non è argmax
  have hu₁lt : l u₁ < l v := by
    rcases lt_or_eq_of_le (hlmax u₁ hu₁T) with h | h
    · exact h
    · exact absurd (hlchar u₁ hu₁T h) hu₁v
  -- w ortogonale alla direzione di e₁, dentro lo span
  obtain ⟨w, hwW, hwne, hwd⟩ := esiste_ortogonale_nello_span
    (le_of_eq hdim.symm) (u₁ - v)
  -- un vertice dove ⟪w,·⟫ si muove
  obtain ⟨u₀, hu₀V, hu₀ne⟩ := exists_vertex_inner_ne Q hvT hwW hwne
  -- senza perdita di generalità il lato positivo è abitato:
  -- costruzione parametrizzata dal segno
  have costruzione : ∀ w' : E n, ⟪w', u₁ - v⟫ = 0 →
      (∃ u ∈ Q.vertices, ⟪w', v⟫ < ⟪w', u⟫) →
      ∃ e₂ : Set (E n), Q.IsFace e₂ ∧ faceDim e₂ = 1 ∧ v ∈ e₂ ∧ e₂ ≠ e₁ := by
    intro w' hw'd hup
    obtain ⟨ux, huxV, huxgt⟩ := hup
    -- i vertici dal lato positivo
    set S : Finset (E n) := Q.vertices.filter (fun u => ⟪w', v⟫ < ⟪w', u⟫)
      with hS
    have hSne : S.Nonempty := ⟨ux, Finset.mem_filter.mpr ⟨huxV, huxgt⟩⟩
    -- il rapporto critico
    set r : E n → ℝ := fun u => (l v - l u) / (⟪w', u⟫ - ⟪w', v⟫) with hr
    obtain ⟨us, husS, husmin⟩ := S.exists_min_image r hSne
    have husV : us ∈ Q.vertices := (Finset.mem_filter.mp husS).1
    have husgt : ⟪w', v⟫ < ⟪w', us⟫ := (Finset.mem_filter.mp husS).2
    have husne : us ≠ v := by
      intro h
      rw [h] at husgt
      exact lt_irrefl _ husgt
    have husT : us ∈ Q.toSet := subset_convexHull ℝ _ husV
    have huslt : l us < l v := by
      rcases lt_or_eq_of_le (hlmax us husT) with h | h
      · exact h
      · exact absurd (hlchar us husT h) husne
    set t : ℝ := r us with ht
    have htpos : 0 < t := by
      rw [ht, hr]
      apply div_pos
      · linarith
      · linarith
    -- il funzionale ruotato
    set ψ : E n →L[ℝ] ℝ := l + t • innerSL ℝ w' with hψ
    have hψval : ∀ y : E n, ψ y = l y + t * ⟪w', y⟫ := by
      intro y
      rw [hψ]
      simp
    -- tutti i vertici stanno sotto ψ v
    have hvert : ∀ u ∈ Q.vertices, ψ u ≤ ψ v := by
      intro u huV
      rw [hψval, hψval]
      by_cases hside : ⟪w', v⟫ < ⟪w', u⟫
      · -- lato positivo: il rapporto domina
        have huS : u ∈ S := Finset.mem_filter.mpr ⟨huV, hside⟩
        have hrle : t ≤ r u := husmin u huS
        have hgap : (0:ℝ) < ⟪w', u⟫ - ⟪w', v⟫ := by linarith
        have h1 : t * (⟪w', u⟫ - ⟪w', v⟫) ≤ r u * (⟪w', u⟫ - ⟪w', v⟫) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have h2 : r u * (⟪w', u⟫ - ⟪w', v⟫) = l v - l u := by
          rw [hr]
          field_simp
        nlinarith
      · -- lato non positivo: entrambi i pezzi scendono
        push_neg at hside
        have h1 : l u ≤ l v := hlmax u (subset_convexHull ℝ _ huV)
        have h2 : t * ⟪w', u⟫ ≤ t * ⟪w', v⟫ :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    -- estensione all'hull: il semispazio è convesso
    have hbody : ∀ y ∈ Q.toSet, ψ y ≤ ψ v := by
      intro y hy
      have hconv : Convex ℝ {z : E n | ψ z ≤ ψ v} := by
        apply convex_halfSpace_le
        exact ψ.toLinearMap.isLinear
      have hsub : (Q.vertices : Set (E n)) ⊆ {z : E n | ψ z ≤ ψ v} := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      have := convexHull_min hsub hconv
      exact this hy
    -- la faccia argmax di ψ
    set F : Set (E n) := {x ∈ Q.toSet | ∀ y ∈ Q.toSet, ψ y ≤ ψ x} with hF
    have hvF : v ∈ F := ⟨hvT, hbody⟩
    have hFface : Q.IsFace F := by
      refine ⟨fun _ => ⟨ψ, rfl⟩, ⟨v, hvF⟩⟩
    -- il vertice critico è in F: pareggio esatto
    have htie : ψ us = ψ v := by
      rw [hψval, hψval]
      have hgap : (0:ℝ) < ⟪w', us⟫ - ⟪w', v⟫ := by linarith
      have h2 : t * (⟪w', us⟫ - ⟪w', v⟫) = l v - l us := by
        show (l v - l us) / (⟪w', us⟫ - ⟪w', v⟫) * (⟪w', us⟫ - ⟪w', v⟫) =
          l v - l us
        exact div_mul_cancel₀ _ (ne_of_gt hgap)
      nlinarith [h2]
    have husF : us ∈ F := by
      refine ⟨husT, ?_⟩
      intro y hy
      rw [htie]
      exact hbody y hy
    -- u₁ non può stare in F
    have hu₁F : u₁ ∉ F := by
      intro hmem
      have h1 : ψ u₁ = ψ v :=
        le_antisymm (hbody u₁ hu₁T) (hmem.2 v hvT)
      rw [hψval, hψval] at h1
      have h2 : ⟪w', u₁⟫ = ⟪w', v⟫ := by
        have h3 : ⟪w', u₁ - v⟫ = 0 := hw'd
        rw [inner_sub_right] at h3
        linarith
      have h4 : l u₁ = l v := by
        rw [h2] at h1
        linarith
      exact hu₁v (hlchar u₁ hu₁T h4)
    -- F non è il corpo e non è e₁
    have hFne : F ≠ Q.toSet := by
      intro h
      exact hu₁F (h ▸ hu₁T)
    have hFne₁ : F ≠ e₁ := by
      intro h
      exact hu₁F (h ▸ hu₁e)
    -- la dimensione è esattamente 1
    have hd1 : 1 ≤ Module.finrank ℝ (vectorSpan ℝ F) :=
      finrank_pos_di_due hvF husF husne
    have hd2 : Module.finrank ℝ (vectorSpan ℝ F) < 2 := by
      have hss : F ⊂ Q.toSet :=
        ⟨fun x hx => hx.1, fun hsup => hFne
          (Set.Subset.antisymm (fun x hx => hx.1) hsup)⟩
      have h1 := faceDim_lt_of_ssubset Q hFface (toSet_isFace Q) hss
      have h2 : faceDim Q.toSet = 2 := hdim
      have h3 : Module.finrank ℝ (vectorSpan ℝ F) <
          Module.finrank ℝ (vectorSpan ℝ Q.toSet) := h1
      omega
    refine ⟨F, hFface, ?_, hvF, hFne₁⟩
    show Module.finrank ℝ (vectorSpan ℝ F) = 1
    omega
  -- il segno giusto
  rcases lt_or_gt_of_ne hu₀ne with hlt | hgt
  · -- ⟪w,u₀⟫ < ⟪w,v⟫: si usa −w
    apply costruzione (-w)
    · rw [inner_neg_left, hwd, neg_zero]
    · refine ⟨u₀, hu₀V, ?_⟩
      rw [inner_neg_left, inner_neg_left]
      linarith
  · -- ⟪w,u₀⟫ > ⟪w,v⟫: si usa w
    exact costruzione w hwd ⟨u₀, hu₀V, hgt⟩

end LeanEval.Geometry.PlatonicClassification

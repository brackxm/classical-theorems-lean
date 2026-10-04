import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Diamante

/-!
FASE 3A, F2 — IL DIAMANTE 2D (18 lug 2026).

Un vertice di un poligono (politopo di rango 2) sta in al più due spigoli.
Stessa strategia del diamante 3D, un gradino sotto: i tre spostamenti dai
punti secondi degli spigoli vivono nel `vectorSpan` di rango 2 del poligono,
quindi sono dipendenti; i tre espositori uccidono ciascuno il proprio
termine e lasciano tre relazioni a coefficienti strettamente negativi con
prodotti a segni impossibili. Qui il politopo può vivere in E n qualunque:
conta solo il rango 2 del suo span.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Una faccia di dimensione ≥ 1 contenente `v` contiene un punto ≠ `v`. -/
theorem faccia_ha_secondo_punto {g : Set (E n)} (hd : faceDim g = 1)
    {v : E n} : ∃ p ∈ g, p ≠ v := by
  by_contra hall
  push_neg at hall
  have hsub : g ⊆ ({v} : Set (E n)) := fun p hp => hall p hp
  have hle := vectorSpan_mono ℝ hsub
  rw [vectorSpan_singleton] at hle
  have h0 : Module.finrank ℝ (vectorSpan ℝ g) ≤
      Module.finrank ℝ (⊥ : Submodule ℝ (E n)) := Submodule.finrank_mono hle
  have hb : Module.finrank ℝ (⊥ : Submodule ℝ (E n)) = 0 := finrank_bot ℝ (E n)
  have hd' : Module.finrank ℝ (vectorSpan ℝ g) = 1 := hd
  omega

/-- Due punti distinti in una faccia forzano rango ≥ 1. -/
theorem finrank_pos_di_due {g : Set (E n)} {v p : E n}
    (hv : v ∈ g) (hp : p ∈ g) (hne : p ≠ v) :
    1 ≤ Module.finrank ℝ (vectorSpan ℝ g) := by
  have hmem : p -ᵥ v ∈ vectorSpan ℝ g := vsub_mem_vectorSpan ℝ hp hv
  have hle : Submodule.span ℝ {p -ᵥ v} ≤ vectorSpan ℝ g := by
    rw [Submodule.span_le]
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact hmem
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton (vsub_ne_zero.mpr hne)] at h1
  exact h1

/-- **IL DIAMANTE 2D**: in un politopo di rango 2, tre spigoli a due a due
distinti non possono passare tutti per lo stesso punto. -/
theorem diamante_poligono (R : ConvexPolytope n)
    (hdim : Module.finrank ℝ (vectorSpan ℝ R.toSet) = 2)
    {e₁ e₂ e₃ : Set (E n)}
    (h1 : R.IsFace e₁) (hd1 : faceDim e₁ = 1)
    (h2 : R.IsFace e₂) (hd2 : faceDim e₂ = 1)
    (h3 : R.IsFace e₃) (hd3 : faceDim e₃ = 1)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {v : E n} (hv1 : v ∈ e₁) (hv2 : v ∈ e₂) (hv3 : v ∈ e₃) : False := by
  classical
  obtain ⟨l₁, hmem₁, hmax₁⟩ := espositore_di_faccia R h1
  obtain ⟨l₂, hmem₂, hmax₂⟩ := espositore_di_faccia R h2
  obtain ⟨l₃, hmem₃, hmax₃⟩ := espositore_di_faccia R h3
  obtain ⟨p₁, hp1, hp1v⟩ := faccia_ha_secondo_punto hd1 (v := v)
  obtain ⟨p₂, hp2, hp2v⟩ := faccia_ha_secondo_punto hd2 (v := v)
  obtain ⟨p₃, hp3, hp3v⟩ := faccia_ha_secondo_punto hd3 (v := v)
  -- costanza dell'espositore sulla propria faccia
  have costanza : ∀ {D : Set (E n)} {lD : E n →L[ℝ] ℝ},
      (∀ y ∈ D, y ∈ R.toSet ∧ ∀ z ∈ R.toSet, lD z ≤ lD y) →
      ∀ {y y' : E n}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  -- il punto secondo di uno spigolo non sta in un altro spigolo
  have fuori : ∀ {ei ej : Set (E n)}, R.IsFace ei → R.IsFace ej → ei ≠ ej →
      faceDim ei = 1 → faceDim ej = 1 → v ∈ ei → v ∈ ej →
      ∀ {p : E n}, p ∈ ej → p ≠ v → p ∉ ei := by
    intro ei ej hei hej hne hdi hdj hvi hvj p hpj hpv hpi
    have hint : R.IsFace (ei ∩ ej) := ⟨hei.1.inter hej.1, ⟨v, hvi, hvj⟩⟩
    have hssub : ei ∩ ej ⊂ ei := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have hij : ei ⊆ ej := fun z hz => (hsup hz).2
      have hss : ei ⊂ ej := ⟨hij, fun h => hne (Set.Subset.antisymm hij h)⟩
      have := faceDim_lt_of_ssubset R hei hej hss
      omega
    have hlt := faceDim_lt_of_ssubset R hint hei hssub
    have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) :=
      finrank_pos_di_due ⟨hvi, hvj⟩ ⟨hpi, hpj⟩ hpv
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) < 1 := by
      have h : Module.finrank ℝ (vectorSpan ℝ (ei ∩ ej)) <
          Module.finrank ℝ (vectorSpan ℝ ei) := hlt
      have hdi' : Module.finrank ℝ (vectorSpan ℝ ei) = 1 := hdi
      omega
    omega
  -- le sei disuguaglianze strette
  have strict : ∀ {ei ej : Set (E n)} {li : E n →L[ℝ] ℝ},
      R.IsFace ei → R.IsFace ej → ei ≠ ej →
      faceDim ei = 1 → faceDim ej = 1 → v ∈ ei → v ∈ ej →
      (∀ y ∈ ei, y ∈ R.toSet ∧ ∀ z ∈ R.toSet, li z ≤ li y) →
      (∀ q ∈ R.toSet, (∀ z ∈ R.toSet, li z ≤ li q) → q ∈ ei) →
      ∀ {p : E n}, p ∈ ej → p ≠ v → li p < li v := by
    intro ei ej li hei hej hne hdi hdj hvi hvj hmem hmax p hpj hpv
    have hpR : p ∈ R.toSet := face_subset_toSet R hej hpj
    have hle : li p ≤ li v := (hmem v hvi).2 p hpR
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hpi : p ∈ ei := hmax p hpR
        (fun z hz => le_trans ((hmem v hvi).2 z hz) (le_of_eq h.symm))
      exact fuori hei hej hne hdi hdj hvi hvj hpj hpv hpi
  have s12 := strict h1 h2 h12 hd1 hd2 hv1 hv2 hmem₁ hmax₁ hp2 hp2v
  have s13 := strict h1 h3 h13 hd1 hd3 hv1 hv3 hmem₁ hmax₁ hp3 hp3v
  have s21 := strict h2 h1 (Ne.symm h12) hd2 hd1 hv2 hv1 hmem₂ hmax₂ hp1 hp1v
  have s23 := strict h2 h3 h23 hd2 hd3 hv2 hv3 hmem₂ hmax₂ hp3 hp3v
  have s31 := strict h3 h1 (Ne.symm h13) hd3 hd1 hv3 hv1 hmem₃ hmax₃ hp1 hp1v
  have s32 := strict h3 h2 (Ne.symm h23) hd3 hd2 hv3 hv2 hmem₃ hmax₃ hp2 hp2v
  -- tre spostamenti nel rango 2: dipendenti
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 3 =>
      if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v else p₃ - v) := by
    intro hli
    have hcard : Module.finrank ℝ (Submodule.span ℝ
        (Set.range (fun i : Fin 3 =>
          if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v
          else p₃ - v))) = 3 := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    have hsp : Submodule.span ℝ (Set.range (fun i : Fin 3 =>
        if i.val = 0 then p₁ - v else if i.val = 1 then p₂ - v
        else p₃ - v)) ≤ vectorSpan ℝ R.toSet := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h1 hp1)
          (face_subset_toSet R h1 hv1)
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h2 hp2)
          (face_subset_toSet R h2 hv2)
      · exact vsub_mem_vectorSpan ℝ (face_subset_toSet R h3 hp3)
          (face_subset_toSet R h3 hv3)
    have h3' := Submodule.finrank_mono hsp
    omega
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_three] at hgsum
  have hgsum3 : gc 0 • (p₁ - v) + gc 1 • (p₂ - v) + gc 2 • (p₃ - v) = 0 :=
    hgsum
  have hnz3 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr hgne)
  -- applicazione dei tre espositori
  have hM1 := congrArg (fun w => l₁ w) hgsum3
  have hM2 := congrArg (fun w => l₂ w) hgsum3
  have hM3 := congrArg (fun w => l₃ w) hgsum3
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hM1 hM2 hM3
  have e11 : l₁ (p₁ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₁ hp1 hv1
    linarith
  have e22 : l₂ (p₂ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₂ hp2 hv2
    linarith
  have e33 : l₃ (p₃ - v) = 0 := by
    rw [map_sub]
    have h := costanza hmem₃ hp3 hv3
    linarith
  have rel₁ : gc 1 * l₁ (p₂ - v) + gc 2 * l₁ (p₃ - v) = 0 := by
    rw [e11] at hM1
    linarith
  have rel₂ : gc 0 * l₂ (p₁ - v) + gc 2 * l₂ (p₃ - v) = 0 := by
    rw [e22] at hM2
    linarith
  have rel₃ : gc 0 * l₃ (p₁ - v) + gc 1 * l₃ (p₂ - v) = 0 := by
    rw [e33] at hM3
    linarith
  -- le sei negatività
  have na : l₁ (p₂ - v) < 0 := by rw [map_sub]; linarith [s12]
  have nb : l₁ (p₃ - v) < 0 := by rw [map_sub]; linarith [s13]
  have nc : l₂ (p₁ - v) < 0 := by rw [map_sub]; linarith [s21]
  have nd : l₂ (p₃ - v) < 0 := by rw [map_sub]; linarith [s23]
  have ne' : l₃ (p₁ - v) < 0 := by rw [map_sub]; linarith [s31]
  have nf : l₃ (p₂ - v) < 0 := by rw [map_sub]; linarith [s32]
  -- nessun coefficiente è nullo
  have hα : gc 0 ≠ 0 := by
    intro h0
    have hγ : gc 2 = 0 := by
      have hr : gc 2 * l₂ (p₃ - v) = 0 := by
        rw [h0] at rel₂
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nd)
    have hβ : gc 1 = 0 := by
      have hr : gc 1 * l₃ (p₂ - v) = 0 := by
        rw [h0] at rel₃
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nf)
    rcases hnz3 with h | h | h
    · exact h h0
    · exact h hβ
    · exact h hγ
  have hβ : gc 1 ≠ 0 := by
    intro h1'
    have hγ : gc 2 = 0 := by
      have hr : gc 2 * l₁ (p₃ - v) = 0 := by
        rw [h1'] at rel₁
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nb)
    have hα0 : gc 0 = 0 := by
      have hr : gc 0 * l₃ (p₁ - v) = 0 := by
        rw [h1'] at rel₃
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt ne')
    rcases hnz3 with h | h | h
    · exact h hα0
    · exact h h1'
    · exact h hγ
  have hγ : gc 2 ≠ 0 := by
    intro h2'
    have hβ0 : gc 1 = 0 := by
      have hr : gc 1 * l₁ (p₂ - v) = 0 := by
        rw [h2'] at rel₁
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt na)
    have hα0 : gc 0 = 0 := by
      have hr : gc 0 * l₂ (p₁ - v) = 0 := by
        rw [h2'] at rel₂
        linarith
      rcases mul_eq_zero.mp hr with h | h
      · exact h
      · exact absurd h (ne_of_lt nc)
    rcases hnz3 with h | h | h
    · exact h hα0
    · exact h hβ0
    · exact h h2'
  -- i tre prodotti a segni opposti: impossibile
  have hβγ : gc 1 * gc 2 < 0 := segno_opposto rel₁ na nb hβ hγ
  have hαγ : gc 0 * gc 2 < 0 := segno_opposto rel₂ nc nd hα hγ
  have hαβ : gc 0 * gc 1 < 0 := segno_opposto rel₃ ne' nf hα hβ
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) := mul_pos_of_neg_of_neg hαβ hαγ
  nlinarith [hpos, hβγ, sq_nonneg (gc 0)]

end LeanEval.Geometry.PlatonicClassification

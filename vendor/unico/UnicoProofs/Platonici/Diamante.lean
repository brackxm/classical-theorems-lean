import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere

/-!
FASE 3A — IL DIAMANTE (18 lug 2026).

La proprietà del diamante in dimensione 3, forma forte: tre faccette a due a
due distinte di un politopo in ℝ³ non possono condividere due punti distinti.
Dimostrazione senza quozienti: gli espositori delle tre faccette si annullano
sulla direzione dello spigolo comune; scelto in ogni faccetta un punto fuori
dalla retta dello spigolo, i tre spostamenti più la direzione dello spigolo
sono quattro vettori in ℝ³, quindi dipendenti; applicando i tre espositori
alla relazione di dipendenza restano tre equazioni a coefficienti strettamente
negativi che impongono ai prodotti dei coefficienti tre segni a due a due
opposti: impossibile. Corollario: uno spigolo sta in al più due faccette
(la forma quantificata attesa da `EdgeInAtMostTwoFacets`).
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Estrazione dell'espositore di una faccia: appartenenza e massimalità. -/
theorem espositore_di_faccia (P : ConvexPolytope n) {g : Set (E n)}
    (hg : P.IsFace g) :
    ∃ l : E n →L[ℝ] ℝ,
      (∀ y ∈ g, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, l z ≤ l y) ∧
      (∀ q ∈ P.toSet, (∀ z ∈ P.toSet, l z ≤ l q) → q ∈ g) := by
  obtain ⟨l, hl⟩ := hg.1 hg.2
  refine ⟨l, ?_, ?_⟩
  · intro y hy
    rw [hl] at hy
    exact ⟨hy.1, hy.2⟩
  · intro q hq hmax
    rw [hl]
    exact ⟨hq, hmax⟩

/-- La retta per due punti distinti ha direzione di rango 1. -/
theorem finrank_direction_retta {v x : E n} (hvx : v ≠ x) :
    Module.finrank ℝ ((affineSpan ℝ ({v, x} : Set (E n))).direction) = 1 := by
  rw [direction_affineSpan, vectorSpan_pair]
  exact finrank_span_singleton (vsub_ne_zero.mpr hvx)

/-- Un insieme di rango ≤ 1 contenente due punti distinti ha per span affine
la retta per quei due punti. -/
theorem affineSpan_eq_retta {g : Set (E n)} {v x : E n} (hvx : v ≠ x)
    (hvg : v ∈ g) (hxg : x ∈ g)
    (hdim : Module.finrank ℝ (vectorSpan ℝ g) ≤ 1) :
    affineSpan ℝ g = affineSpan ℝ ({v, x} : Set (E n)) := by
  have hsub : ({v, x} : Set (E n)) ⊆ g := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz1
    · exact hvg
    · rcases Set.mem_singleton_iff.mp hz1 with rfl
      exact hxg
  have hle : affineSpan ℝ ({v, x} : Set (E n)) ≤ affineSpan ℝ g :=
    affineSpan_mono ℝ hsub
  have hdireq : (affineSpan ℝ ({v, x} : Set (E n))).direction =
      (affineSpan ℝ g).direction := by
    apply Submodule.eq_of_le_of_finrank_le (AffineSubspace.direction_le hle)
    rw [finrank_direction_retta hvx, direction_affineSpan]
    exact hdim
  exact (AffineSubspace.ext_of_direction_eq hdireq
    ⟨v, subset_affineSpan ℝ _ (Set.mem_insert v {x}),
      subset_affineSpan ℝ _ hvg⟩).symm

/-- In un insieme di rango 2 c'è un punto fuori da ogni retta. -/
theorem punto_fuori_retta {g : Set (E n)} (v x : E n) (hvx : v ≠ x)
    (hdim : faceDim g = 2) :
    ∃ p ∈ g, p ∉ affineSpan ℝ ({v, x} : Set (E n)) := by
  by_contra hall
  push_neg at hall
  have hsub : g ⊆ (affineSpan ℝ ({v, x} : Set (E n)) : Set (E n)) := hall
  have hle : affineSpan ℝ g ≤ affineSpan ℝ ({v, x} : Set (E n)) :=
    affineSpan_le.mpr hsub
  have h1 : Module.finrank ℝ ((affineSpan ℝ g).direction) ≤
      Module.finrank ℝ ((affineSpan ℝ ({v, x} : Set (E n))).direction) :=
    Submodule.finrank_mono (AffineSubspace.direction_le hle)
  rw [finrank_direction_retta hvx, direction_affineSpan] at h1
  have hdim' : Module.finrank ℝ (vectorSpan ℝ g) = 2 := hdim
  omega

/-- Se due facce distinte di dimensione 2 condividono due punti distinti,
un punto dell'una fuori dalla retta comune non sta nell'altra. -/
theorem fuori_dalla_terza (P : ConvexPolytope n) {Φ Ψ : Set (E n)} {v x : E n}
    (hΦ : P.IsFace Φ) (hΨ : P.IsFace Ψ) (hne : Φ ≠ Ψ)
    (hdΦ : faceDim Φ = 2) (hdΨ : faceDim Ψ = 2) (hvx : v ≠ x)
    (hvΦ : v ∈ Φ) (hxΦ : x ∈ Φ) (hvΨ : v ∈ Ψ) (hxΨ : x ∈ Ψ)
    {p : E n} (hpΨ : p ∈ Ψ)
    (hpL : p ∉ affineSpan ℝ ({v, x} : Set (E n))) : p ∉ Φ := by
  intro hpΦ
  have hint : P.IsFace (Φ ∩ Ψ) := ⟨hΦ.1.inter hΨ.1, ⟨v, hvΦ, hvΨ⟩⟩
  have hssub : Φ ∩ Ψ ⊂ Φ := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hΦΨ : Φ ⊆ Ψ := fun z hz => (hsup hz).2
    have hss : Φ ⊂ Ψ := ⟨hΦΨ, fun h => hne (Set.Subset.antisymm hΦΨ h)⟩
    have := faceDim_lt_of_ssubset P hΦ hΨ hss
    omega
  have hdim : faceDim (Φ ∩ Ψ) < 2 := by
    have := faceDim_lt_of_ssubset P hint hΦ hssub
    omega
  have hdim' : Module.finrank ℝ (vectorSpan ℝ (Φ ∩ Ψ)) ≤ 1 := by
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Φ ∩ Ψ)) < 2 := hdim
    omega
  have hspan : affineSpan ℝ (Φ ∩ Ψ) = affineSpan ℝ ({v, x} : Set (E n)) :=
    affineSpan_eq_retta hvx ⟨hvΦ, hvΨ⟩ ⟨hxΦ, hxΨ⟩ hdim'
  apply hpL
  rw [← hspan]
  exact subset_affineSpan ℝ _ ⟨hpΦ, hpΨ⟩

/-- Il valore dell'espositore su un punto di un'altra faccia, fuori dalla
retta comune, è strettamente sotto il massimo. -/
theorem strict_su_terza (P : ConvexPolytope n) {Φ Ψ : Set (E n)} {v x : E n}
    {lΦ : E n →L[ℝ] ℝ}
    (hΦ : P.IsFace Φ) (hΨ : P.IsFace Ψ) (hne : Φ ≠ Ψ)
    (hdΦ : faceDim Φ = 2) (hdΨ : faceDim Ψ = 2) (hvx : v ≠ x)
    (hvΦ : v ∈ Φ) (hxΦ : x ∈ Φ) (hvΨ : v ∈ Ψ) (hxΨ : x ∈ Ψ)
    (hmem : ∀ y ∈ Φ, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, lΦ z ≤ lΦ y)
    (hmax : ∀ q ∈ P.toSet, (∀ z ∈ P.toSet, lΦ z ≤ lΦ q) → q ∈ Φ)
    {p : E n} (hpΨ : p ∈ Ψ)
    (hpL : p ∉ affineSpan ℝ ({v, x} : Set (E n))) :
    lΦ p < lΦ v := by
  have hpP : p ∈ P.toSet := face_subset_toSet P hΨ hpΨ
  have hle : lΦ p ≤ lΦ v := (hmem v hvΦ).2 p hpP
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    have hpΦ : p ∈ Φ := hmax p hpP
      (fun z hz => le_trans ((hmem v hvΦ).2 z hz) (le_of_eq h.symm))
    exact fuori_dalla_terza P hΦ hΨ hne hdΦ hdΨ hvx hvΦ hxΦ hvΨ hxΨ hpΨ hpL hpΦ

/-- Da `gi·a + gj·b = 0` con `a, b < 0` e `gi, gj ≠ 0` segue `gi·gj < 0`. -/
theorem segno_opposto {gi gj a b : ℝ} (hrel : gi * a + gj * b = 0)
    (ha : a < 0) (hb : b < 0) (hgi : gi ≠ 0) (hgj : gj ≠ 0) :
    gi * gj < 0 := by
  rcases lt_or_gt_of_ne hgi with h | h
  · have h1 : 0 < gi * a := mul_pos_of_neg_of_neg h ha
    have h3 : 0 < gj := by
      by_contra hle
      push_neg at hle
      have h2 : 0 ≤ (-gj) * (-b) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    exact mul_neg_of_neg_of_pos h h3
  · have h1 : gi * a < 0 := mul_neg_of_pos_of_neg h ha
    have h3 : gj < 0 := by
      by_contra hle
      push_neg at hle
      have h2 : 0 ≤ gj * (-b) := mul_nonneg hle (by linarith)
      nlinarith
    exact mul_neg_of_pos_of_neg h h3

/-- **IL DIAMANTE, forma forte**: in un politopo di ℝ³ tre faccette a due a
due distinte non possono condividere due punti distinti. -/
theorem diamante (P : ConvexPolytope 3) {A B C : Set (E 3)}
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (hC : P.IsFace C) (hdC : faceDim C = 2)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    {v x : E 3} (hvx : v ≠ x)
    (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    (hxA : x ∈ A) (hxB : x ∈ B) (hxC : x ∈ C) : False := by
  classical
  obtain ⟨lA, hmemA, hmaxA⟩ := espositore_di_faccia P hA
  obtain ⟨lB, hmemB, hmaxB⟩ := espositore_di_faccia P hB
  obtain ⟨lC, hmemC, hmaxC⟩ := espositore_di_faccia P hC
  obtain ⟨p1, hp1A, hp1L⟩ := punto_fuori_retta (g := A) v x hvx hdA
  obtain ⟨p2, hp2B, hp2L⟩ := punto_fuori_retta (g := B) v x hvx hdB
  obtain ⟨p3, hp3C, hp3L⟩ := punto_fuori_retta (g := C) v x hvx hdC
  -- costanza dell'espositore sulla propria faccia
  have costanza : ∀ {D : Set (E 3)} {lD : E 3 →L[ℝ] ℝ},
      (∀ y ∈ D, y ∈ P.toSet ∧ ∀ z ∈ P.toSet, lD z ≤ lD y) →
      ∀ {y y' : E 3}, y ∈ D → y' ∈ D → lD y = lD y' := by
    intro D lD hmem y y' hy hy'
    exact le_antisymm ((hmem y' hy').2 y (hmem y hy).1)
      ((hmem y hy).2 y' (hmem y' hy').1)
  -- le sei disuguaglianze strette
  have sAB := strict_su_terza P hA hB hAB hdA hdB hvx hvA hxA hvB hxB
    hmemA hmaxA hp2B hp2L
  have sAC := strict_su_terza P hA hC hAC hdA hdC hvx hvA hxA hvC hxC
    hmemA hmaxA hp3C hp3L
  have sBA := strict_su_terza P hB hA (Ne.symm hAB) hdB hdA hvx hvB hxB hvA hxA
    hmemB hmaxB hp1A hp1L
  have sBC := strict_su_terza P hB hC hBC hdB hdC hvx hvB hxB hvC hxC
    hmemB hmaxB hp3C hp3L
  have sCA := strict_su_terza P hC hA (Ne.symm hAC) hdC hdA hvx hvC hxC hvA hxA
    hmemC hmaxC hp1A hp1L
  have sCB := strict_su_terza P hC hB (Ne.symm hBC) hdC hdB hvx hvC hxC hvB hxB
    hmemC hmaxC hp2B hp2L
  -- quattro vettori in ℝ³: dipendenti
  have hdep : ¬ LinearIndependent ℝ (fun i : Fin 4 =>
      if i.val = 0 then p1 - v else if i.val = 1 then p2 - v
      else if i.val = 2 then p3 - v else x - v) := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace] at hcard
    have h4 : (4 : ℕ) ≤ 3 := by simpa [Fintype.card_fin] using hcard
    omega
  obtain ⟨gc, hgsum, i0, hgne⟩ := Fintype.not_linearIndependent_iff.mp hdep
  rw [Fin.sum_univ_four] at hgsum
  have hgsum4 : gc 0 • (p1 - v) + gc 1 • (p2 - v) + gc 2 • (p3 - v) +
      gc 3 • (x - v) = 0 := hgsum
  have hnz4 : gc 0 ≠ 0 ∨ gc 1 ≠ 0 ∨ gc 2 ≠ 0 ∨ gc 3 ≠ 0 := by
    rcases i0 with ⟨iv, hi⟩
    interval_cases iv
    · exact Or.inl hgne
    · exact Or.inr (Or.inl hgne)
    · exact Or.inr (Or.inr (Or.inl hgne))
    · exact Or.inr (Or.inr (Or.inr hgne))
  -- applicazione dei tre espositori
  have hMA := congrArg (fun w => lA w) hgsum4
  have hMB := congrArg (fun w => lB w) hgsum4
  have hMC := congrArg (fun w => lC w) hgsum4
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hMA hMB hMC
  -- gli azzeramenti: punto proprio e direzione dello spigolo
  have eA1 : lA (p1 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemA hp1A hvA
    linarith
  have eAt : lA (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemA hxA hvA
    linarith
  have eB2 : lB (p2 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemB hp2B hvB
    linarith
  have eBt : lB (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemB hxB hvB
    linarith
  have eC3 : lC (p3 - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemC hp3C hvC
    linarith
  have eCt : lC (x - v) = 0 := by
    rw [map_sub]
    have h := costanza hmemC hxC hvC
    linarith
  -- le tre relazioni residue
  have relA : gc 1 * lA (p2 - v) + gc 2 * lA (p3 - v) = 0 := by
    rw [eA1, eAt] at hMA
    linarith
  have relB : gc 0 * lB (p1 - v) + gc 2 * lB (p3 - v) = 0 := by
    rw [eB2, eBt] at hMB
    linarith
  have relC : gc 0 * lC (p1 - v) + gc 1 * lC (p2 - v) = 0 := by
    rw [eC3, eCt] at hMC
    linarith
  -- le sei negatività
  have ha : lA (p2 - v) < 0 := by rw [map_sub]; linarith [sAB]
  have hb : lA (p3 - v) < 0 := by rw [map_sub]; linarith [sAC]
  have hc : lB (p1 - v) < 0 := by rw [map_sub]; linarith [sBA]
  have hd : lB (p3 - v) < 0 := by rw [map_sub]; linarith [sBC]
  have he : lC (p1 - v) < 0 := by rw [map_sub]; linarith [sCA]
  have hf : lC (p2 - v) < 0 := by rw [map_sub]; linarith [sCB]
  -- collasso: se i primi tre coefficienti sono nulli, tutti lo sono
  have hxv0 : x - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hvx)
  have hcollasso : gc 0 = 0 → gc 1 = 0 → gc 2 = 0 → False := by
    intro h0 h1 h2
    rw [h0, h1, h2] at hgsum4
    simp only [zero_smul, zero_add] at hgsum4
    rcases smul_eq_zero.mp hgsum4 with h3 | h3
    · rcases hnz4 with h | h | h | h
      · exact h h0
      · exact h h1
      · exact h h2
      · exact h h3
    · exact hxv0 h3
  -- nessuno dei tre coefficienti è nullo
  have hα : gc 0 ≠ 0 := by
    intro h0
    have hγ : gc 2 = 0 := by
      have hrb : gc 2 * lB (p3 - v) = 0 := by
        rw [h0] at relB
        linarith
      rcases mul_eq_zero.mp hrb with h | h
      · exact h
      · exact absurd h (ne_of_lt hd)
    have hβ : gc 1 = 0 := by
      have hrc : gc 1 * lC (p2 - v) = 0 := by
        rw [h0] at relC
        linarith
      rcases mul_eq_zero.mp hrc with h | h
      · exact h
      · exact absurd h (ne_of_lt hf)
    exact hcollasso h0 hβ hγ
  have hβ : gc 1 ≠ 0 := by
    intro h1
    have hγ : gc 2 = 0 := by
      have hra : gc 2 * lA (p3 - v) = 0 := by
        rw [h1] at relA
        linarith
      rcases mul_eq_zero.mp hra with h | h
      · exact h
      · exact absurd h (ne_of_lt hb)
    have hα0 : gc 0 = 0 := by
      have hrc : gc 0 * lC (p1 - v) = 0 := by
        rw [h1] at relC
        linarith
      rcases mul_eq_zero.mp hrc with h | h
      · exact h
      · exact absurd h (ne_of_lt he)
    exact hcollasso hα0 h1 hγ
  have hγ : gc 2 ≠ 0 := by
    intro h2
    have hβ0 : gc 1 = 0 := by
      have hra : gc 1 * lA (p2 - v) = 0 := by
        rw [h2] at relA
        linarith
      rcases mul_eq_zero.mp hra with h | h
      · exact h
      · exact absurd h (ne_of_lt ha)
    have hα0 : gc 0 = 0 := by
      have hrb : gc 0 * lB (p1 - v) = 0 := by
        rw [h2] at relB
        linarith
      rcases mul_eq_zero.mp hrb with h | h
      · exact h
      · exact absurd h (ne_of_lt hc)
    exact hcollasso hα0 hβ0 h2
  -- i tre prodotti a segni opposti: impossibile
  have hβγ : gc 1 * gc 2 < 0 := segno_opposto relA ha hb hβ hγ
  have hαγ : gc 0 * gc 2 < 0 := segno_opposto relB hc hd hα hγ
  have hαβ : gc 0 * gc 1 < 0 := segno_opposto relC he hf hα hβ
  have hpos : 0 < (gc 0 * gc 1) * (gc 0 * gc 2) := mul_pos_of_neg_of_neg hαβ hαγ
  nlinarith [hpos, hβγ, sq_nonneg (gc 0)]

/-- **Uno spigolo sta in al più due faccette** — la forma quantificata
attesa dal predicato `EdgeInAtMostTwoFacets` del fascicolo sul fan. -/
theorem spigolo_in_due_faccette (P : ConvexPolytope 3) (v : E 3)
    ⦃A B C : Set (E 3)⦄
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (hC : P.IsFace C) (hdC : faceDim C = 2)
    (hAB : A ≠ B) (hvA : v ∈ A) (hvB : v ∈ B) (hvC : v ∈ C)
    ⦃x : E 3⦄ (hx : x ∈ A ∩ B) (hxv : x ≠ v) (hxC : x ∈ C) :
    C = A ∨ C = B := by
  by_contra hcon
  push_neg at hcon
  exact diamante P hA hdA hB hdB hC hdC hAB
    (fun h => hcon.1 h.symm) (fun h => hcon.2 h.symm)
    (Ne.symm hxv) hvA hvB hvC hx.1 hx.2 hxC

end LeanEval.Geometry.PlatonicClassification

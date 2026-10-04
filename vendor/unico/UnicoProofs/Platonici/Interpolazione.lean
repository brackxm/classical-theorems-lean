import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DueFunzionali
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.Perno

/-!
FASE 3A, Q3-S3 — INTERPOLAZIONE (18 lug 2026).

Il perno viene prima reso parametrico nella direzione ortogonale `w`.
Se la nuova faccia coincide con tutto il politopo, il funzionale perturbato
e' costante sui vertici. Due direzioni indipendenti rendono impossibile che
questo caso degenere si presenti entrambe le volte.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Versione crescente del perno parametrico. Nel caso in cui la faccia
costruita sia tutto il corpo, conserva la costanza del funzionale sui
vertici. -/
theorem perno_parametrico_crescente (P : ConvexPolytope n) {f : Set (E n)}
    (_hf : P.IsFace f) (l : E n →L[ℝ] ℝ)
    (hl : f = {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x})
    (p₀ : E n) (hp₀f : p₀ ∈ f) (w : E n)
    (hwconst : ∀ z ∈ f, inner ℝ w z = inner ℝ w p₀)
    (hup : ∃ u ∈ P.vertices, inner ℝ w p₀ < inner ℝ w u) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧
      (f' ≠ P.toSet ∨
        ∃ t : ℝ, 0 < t ∧ ∃ c : ℝ,
          ∀ v ∈ P.vertices, l v + t * inner ℝ w v = c) := by
  classical
  obtain ⟨u, huV, huup⟩ := hup
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  set M : ℝ := l p₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    rw [hl] at hz hp₀f
    exact le_antisymm (hp₀f.2 z hz.1) (hz.2 p₀ hp₀f.1)
  have hlmax : ∀ y ∈ P.toSet, l y ≤ M := by
    intro y hy
    rw [hl] at hp₀f
    exact hp₀f.2 y hy
  have hl_strict : ∀ v ∈ P.vertices, v ∉ f → l v < M := by
    intro v hvV hvf
    have hvT : v ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hvV)
    rcases lt_or_eq_of_le (hlmax v hvT) with h | h
    · exact h
    · exfalso
      apply hvf
      rw [hl]
      exact ⟨hvT, fun y hy => h ▸ hlmax y hy⟩
  have huf : u ∉ f := by
    intro h
    have := hwconst u h
    linarith

  set l₂ : E n →L[ℝ] ℝ := innerSL ℝ w with hl₂
  have hl₂const : ∀ z ∈ f, l₂ z = l₂ p₀ := by
    intro z hz
    simpa [l₂] using hwconst z hz
  have hl₂up : l₂ p₀ < l₂ u := by simpa [l₂] using huup

  set Vup : Finset (E n) :=
    P.vertices.filter (fun v => l₂ p₀ < l₂ v) with hVup
  have huUp : u ∈ Vup := by simp [hVup, huV, hl₂up]
  have hVupne : Vup.Nonempty := ⟨u, huUp⟩
  set ratio : E n → ℝ :=
    fun v => (M - l v) / (l₂ v - l₂ p₀) with hratio
  have hratio_pos : ∀ v ∈ Vup, 0 < ratio v := by
    intro v hvUp
    have hv := Finset.mem_filter.mp hvUp
    have hvnf : v ∉ f := by
      intro hvf
      have := hl₂const v hvf
      linarith
    have hnum : 0 < M - l v := by
      have := hl_strict v hv.1 hvnf
      linarith
    have hden : 0 < l₂ v - l₂ p₀ := by linarith
    rw [hratio]
    exact div_pos hnum hden
  set R : Finset ℝ := Vup.image ratio with hR
  have hRne : R.Nonempty := hVupne.image ratio
  set t : ℝ := R.min' hRne with ht
  have htpos : 0 < t := by
    have htmem : t ∈ R := by
      rw [ht]
      exact Finset.min'_mem R hRne
    obtain ⟨v, hvUp, hvt⟩ :=
      Finset.mem_image.mp (by simpa [hR] using htmem)
    rw [← hvt]
    exact hratio_pos v hvUp

  set L : E n →L[ℝ] ℝ := l + t • l₂ with hL
  have hLapp : ∀ x, L x = l x + t * l₂ x := by
    intro x
    simp [hL, smul_eq_mul]
  have hvert : ∀ v ∈ (P.vertices : Set (E n)),
      L v ≤ M + t * l₂ p₀ := by
    intro v hvS
    have hvV : v ∈ P.vertices := by exact_mod_cast hvS
    have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hvS
    by_cases hvup : l₂ p₀ < l₂ v
    · have hvUp : v ∈ Vup := by simp [hVup, hvV, hvup]
      have hratioR : ratio v ∈ R := by
        rw [hR]
        exact Finset.mem_image_of_mem ratio hvUp
      have htle : t ≤ ratio v := by
        rw [ht]
        exact Finset.min'_le R (ratio v) hratioR
      have hden : 0 < l₂ v - l₂ p₀ := by linarith
      have hmul : t * (l₂ v - l₂ p₀) ≤ M - l v := by
        calc
          t * (l₂ v - l₂ p₀) ≤ ratio v * (l₂ v - l₂ p₀) :=
            mul_le_mul_of_nonneg_right htle (le_of_lt hden)
          _ = M - l v := by
            rw [hratio]
            field_simp
      rw [hLapp]
      linarith
    · have hlv := hlmax v hvT
      have hl₂v : l₂ v ≤ l₂ p₀ := le_of_not_gt hvup
      rw [hLapp]
      nlinarith
  have hLbound : ∀ y ∈ P.toSet, L y ≤ M + t * l₂ p₀ :=
    le_su_toSet P L hvert

  have htmem : t ∈ R := by
    rw [ht]
    exact Finset.min'_mem R hRne
  obtain ⟨vcrit, hvcritUp, hvcritEq⟩ :=
    Finset.mem_image.mp (by simpa [hR] using htmem)
  have hvcritV : vcrit ∈ P.vertices := (Finset.mem_filter.mp hvcritUp).1
  have hvcritGrow : l₂ p₀ < l₂ vcrit :=
    (Finset.mem_filter.mp hvcritUp).2
  have hvcrit_notf : vcrit ∉ f := by
    intro hvcf
    have := hl₂const vcrit hvcf
    linarith
  have hvcritL : L vcrit = M + t * l₂ p₀ := by
    have hden : l₂ vcrit - l₂ p₀ ≠ 0 := by linarith
    have heq : t * (l₂ vcrit - l₂ p₀) = M - l vcrit := by
      rw [← hvcritEq, hratio]
      field_simp
    rw [hLapp]
    linarith

  set f' : Set (E n) :=
    {x ∈ P.toSet | ∀ y ∈ P.toSet, L y ≤ L x} with hf'def
  have hsub : f ⊆ f' := by
    intro x hxf
    have hxT : x ∈ P.toSet := by
      rw [hl] at hxf
      exact hxf.1
    have hLx : L x = M + t * l₂ p₀ := by
      rw [hLapp, hlf x hxf, hl₂const x hxf]
    refine ⟨hxT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hLx.symm
  have hvcritT : vcrit ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hvcritV)
  have hvcritf' : vcrit ∈ f' := by
    refine ⟨hvcritT, ?_⟩
    intro y hy
    exact (hLbound y hy).trans_eq hvcritL.symm
  have hf'ne : f'.Nonempty := ⟨p₀, hsub hp₀f⟩
  have hf'face : P.IsFace f' := by
    refine ⟨?_, hf'ne⟩
    intro _
    exact ⟨L, rfl⟩
  have hfstrict : f ⊂ f' := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨hsub, ?_⟩
    intro hff'
    apply hvcrit_notf
    rw [hff']
    exact hvcritf'

  refine ⟨f', hf'face, hfstrict, ?_⟩
  by_cases hproper : f' ≠ P.toSet
  · exact Or.inl hproper
  · right
    refine ⟨t, htpos, M + t * inner ℝ w p₀, ?_⟩
    intro v hvV
    have hvT : v ∈ P.toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hvV)
    have hvf' : v ∈ f' := by rw [not_ne_iff.mp hproper]; exact hvT
    have hp₀max : L p₀ ≤ L v := hvf'.2 p₀ hp₀T
    have hLp₀ : L p₀ = M + t * l₂ p₀ := by
      rw [hLapp, hM]
    have hLv : L v = M + t * l₂ p₀ :=
      le_antisymm (hLbound v hvT) (by linarith)
    simpa [hLapp, l₂] using hLv

open Classical in
/-- Perno parametrico senza scelta di orientazione. Il coefficiente della
perturbazione e' non nullo; puo' essere negativo quando `w` va orientato nel
verso opposto. -/
theorem perno_parametrico (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f) (l : E n →L[ℝ] ℝ)
    (hl : f = {x ∈ P.toSet | ∀ y ∈ P.toSet, l y ≤ l x})
    (p₀ : E n) (hp₀f : p₀ ∈ f) (w : E n)
    (hwconst : ∀ z ∈ f, inner ℝ w z = inner ℝ w p₀)
    (hvar : ∃ u ∈ P.vertices, inner ℝ w u ≠ inner ℝ w p₀) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧
      (f' ≠ P.toSet ∨
        ∃ t : ℝ, t ≠ 0 ∧ ∃ c : ℝ,
          ∀ v ∈ P.vertices, l v + t * inner ℝ w v = c) := by
  classical
  obtain ⟨u, huV, hune⟩ := hvar
  rcases lt_or_gt_of_ne hune with hlt | hgt
  · have hup : ∃ u ∈ P.vertices,
        inner ℝ (-w) p₀ < inner ℝ (-w) u := by
      refine ⟨u, huV, ?_⟩
      simpa using hlt
    have hwconst' : ∀ z ∈ f,
        inner ℝ (-w) z = inner ℝ (-w) p₀ := by
      intro z hz
      simpa using congrArg Neg.neg (hwconst z hz)
    obtain ⟨f', hf', hff', halt⟩ :=
      perno_parametrico_crescente P hf l hl p₀ hp₀f (-w) hwconst' hup
    refine ⟨f', hf', hff', ?_⟩
    rcases halt with hproper | ⟨t, htpos, c, hc⟩
    · exact Or.inl hproper
    · right
      refine ⟨-t, by linarith, c, ?_⟩
      intro v hv
      have := hc v hv
      simpa using this
  · have hup : ∃ u ∈ P.vertices,
        inner ℝ w p₀ < inner ℝ w u := ⟨u, huV, hgt⟩
    obtain ⟨f', hf', hff', halt⟩ :=
      perno_parametrico_crescente P hf l hl p₀ hp₀f w hwconst hup
    refine ⟨f', hf', hff', ?_⟩
    rcases halt with hproper | ⟨t, htpos, c, hc⟩
    · exact Or.inl hproper
    · exact Or.inr ⟨t, ne_of_gt htpos, c, hc⟩

open Classical in
/-- Un vettore non nullo nella direzione affine del politopo induce un
funzionale interno non costante sui vertici. -/
theorem exists_vertex_inner_ne (P : ConvexPolytope n) {p w : E n}
    (hp : p ∈ P.toSet) (hw : w ∈ vectorSpan ℝ P.toSet) (hwne : w ≠ 0) :
    ∃ v ∈ P.vertices, inner ℝ w v ≠ inner ℝ w p := by
  classical
  by_contra hall
  push Not at hall
  let A : E n →ᵃ[ℝ] ℝ := (innerSL ℝ w).toLinearMap.toAffineMap
  let C : E n →ᵃ[ℝ] ℝ := AffineMap.const ℝ (E n) (inner ℝ w p)
  have hagree : Set.EqOn A C (P.vertices : Set (E n)) := by
    intro v hv
    change inner ℝ w v = inner ℝ w p
    exact hall v (by exact_mod_cast hv)
  have hspan := AffineMap.eqOn_affineSpan (k := ℝ) hagree
  have hpaff : p ∈ affineSpan ℝ (P.vertices : Set (E n)) := by
    have hpaffT : p ∈ affineSpan ℝ P.toSet :=
      subset_affineSpan ℝ P.toSet hp
    simpa [ConvexPolytope.toSet] using hpaffT
  have hwdir : w ∈ (affineSpan ℝ (P.vertices : Set (E n))).direction := by
    rw [← direction_affineSpan] at hw
    simpa [ConvexPolytope.toSet] using hw
  have hpw : w +ᵥ p ∈ affineSpan ℝ (P.vertices : Set (E n)) :=
    AffineSubspace.vadd_mem_of_mem_direction hwdir hpaff
  have h1 := hspan hpw
  have h2 := hspan hpaff
  have hadd : inner ℝ w (w + p) = inner ℝ w p := by
    simpa [A, C] using h1
  have hzero : inner ℝ w w = 0 := by
    rw [inner_add_right] at hadd
    linarith
  exact hwne (inner_self_eq_zero.mp hzero)

open Classical in
/-- S3: tra una faccia e un politopo con salto di dimensione almeno due
esiste una faccia intermedia propria. -/
theorem interpolazione (P : ConvexPolytope n) {f : Set (E n)}
    (hf : P.IsFace f)
    (hgap : faceDim f + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet)) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' ∧ f' ≠ P.toSet := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨p₀, hp₀f⟩ := hf.2
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  set U : Submodule ℝ (E n) := vectorSpan ℝ f with hU
  set W : Submodule ℝ (E n) := vectorSpan ℝ P.toSet with hW
  have hfT : f ⊆ P.toSet := by
    intro x hx
    rw [hl] at hx
    exact hx.1
  have hUW : U ≤ W := by
    rw [hU, hW]
    exact vectorSpan_mono ℝ hfT
  have hcodim : Module.finrank ℝ U + 2 ≤ Module.finrank ℝ W := by
    simpa [hU, hW, faceDim] using hgap
  obtain ⟨w₁, w₂, hw₁W, hw₂W, hw₁orth, hw₂orth, hLI⟩ :=
    exists_two_orthogonal_indep (U := U) (W := W) hUW hcodim
  have hw₁ne : w₁ ≠ 0 := by
    simpa using hLI.ne_zero 0
  have hw₂ne : w₂ ≠ 0 := by
    simpa using hLI.ne_zero 1
  have hw₁const : ∀ z ∈ f, inner ℝ w₁ z = inner ℝ w₁ p₀ := by
    intro z hz
    have hzU : z - p₀ ∈ U := by
      rw [hU]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := hw₁orth (z - p₀) hzU
    rw [← sub_eq_zero, ← inner_sub_right]
    exact ho
  have hw₂const : ∀ z ∈ f, inner ℝ w₂ z = inner ℝ w₂ p₀ := by
    intro z hz
    have hzU : z - p₀ ∈ U := by
      rw [hU]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := hw₂orth (z - p₀) hzU
    rw [← sub_eq_zero, ← inner_sub_right]
    exact ho
  have hw₁var : ∃ v ∈ P.vertices,
      inner ℝ w₁ v ≠ inner ℝ w₁ p₀ := by
    apply exists_vertex_inner_ne P hp₀T
    · simpa [hW] using hw₁W
    · exact hw₁ne
  have hw₂var : ∃ v ∈ P.vertices,
      inner ℝ w₂ v ≠ inner ℝ w₂ p₀ := by
    apply exists_vertex_inner_ne P hp₀T
    · simpa [hW] using hw₂W
    · exact hw₂ne

  obtain ⟨f₁, hf₁, hff₁, halt₁⟩ :=
    perno_parametrico P hf l hl p₀ hp₀f w₁ hw₁const hw₁var
  rcases halt₁ with hf₁proper | ⟨t₁, ht₁, c₁, hc₁⟩
  · exact ⟨f₁, hf₁, hff₁, hf₁proper⟩
  obtain ⟨f₂, hf₂, hff₂, halt₂⟩ :=
    perno_parametrico P hf l hl p₀ hp₀f w₂ hw₂const hw₂var
  rcases halt₂ with hf₂proper | ⟨t₂, ht₂, c₂, hc₂⟩
  · exact ⟨f₂, hf₂, hff₂, hf₂proper⟩

  exfalso
  set q : E n := t₁ • w₁ - t₂ • w₂ with hq
  have hqW : q ∈ W := by
    exact W.sub_mem (W.smul_mem t₁ hw₁W) (W.smul_mem t₂ hw₂W)
  have hqconst : ∀ v ∈ P.vertices, inner ℝ q v = c₁ - c₂ := by
    intro v hv
    have h1 := hc₁ v hv
    have h2 := hc₂ v hv
    calc
      inner ℝ q v = t₁ * inner ℝ w₁ v - t₂ * inner ℝ w₂ v := by
        rw [hq, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      _ = c₁ - c₂ := by linarith
  obtain ⟨v₀, hv₀V⟩ := P.vertices_nonempty
  have hv₀T : v₀ ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast hv₀V)
  have hqzero : q = 0 := by
    by_contra hqne
    obtain ⟨v, hvV, hvne⟩ := exists_vertex_inner_ne P hv₀T
      (by simpa [hW] using hqW) hqne
    apply hvne
    rw [hqconst v hvV, hqconst v₀ hv₀V]
  have heq : t₁ • w₁ = t₂ • w₂ := by
    exact sub_eq_zero.mp (by simpa [hq] using hqzero)
  have hwrel := congrArg (fun x : E n => t₁⁻¹ • x) heq
  have hwrel' : w₁ = (t₁⁻¹ * t₂) • w₂ := by
    simpa [smul_smul, ht₁] using hwrel
  have hpair := (linearIndependent_fin2.mp hLI).2 (t₁⁻¹ * t₂)
  exact hpair hwrel'.symm

end LeanEval.Geometry.PlatonicClassification

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo

/-!
FASE 3A, Q3-S1 — IL PERNO (18 lug 2026).

Sopra ogni faccia propria di un politopo c'è una faccia strettamente più
grande.  Il secondo funzionale è costruito col residuo ortogonale rispetto
alla direzione affine della faccia; il tempo di perturbazione è il minimo
dei rapporti critici sui vertici sui quali quel funzionale cresce.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- Q3-S1, il passo di perno: ogni faccia propria è contenuta strettamente
in un'altra faccia. -/
theorem perno (P : ConvexPolytope n) {f : Set (E n)} (hf : P.IsFace f)
    (hproper : ∃ v ∈ P.vertices, v ∉ f) :
    ∃ f' : Set (E n), P.IsFace f' ∧ f ⊂ f' := by
  classical
  obtain ⟨l, hl⟩ := hf.1 hf.2
  obtain ⟨p₀, hp₀f⟩ := hf.2
  obtain ⟨u, huV, huf⟩ := hproper
  have hp₀T : p₀ ∈ P.toSet := by
    rw [hl] at hp₀f
    exact hp₀f.1
  have huT : u ∈ P.toSet :=
    subset_convexHull ℝ _ (by exact_mod_cast huV)

  -- Il valore del primo funzionale sulla faccia.
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
    have hvle := hlmax v hvT
    rcases lt_or_eq_of_le hvle with h | h
    · exact h
    · exfalso
      apply hvf
      rw [hl]
      exact ⟨hvT, fun y hy => h ▸ hlmax y hy⟩
  have hlu : l u < M := hl_strict u huV huf

  -- Poiché l è costante su f, è costante anche sul suo affine span.
  -- Il vertice esterno u è quindi automaticamente trasverso.
  have huaff : u ∉ affineSpan ℝ f := by
    intro hu
    let A : AffineSubspace ℝ (E n) :=
      AffineSubspace.mk' p₀ (LinearMap.ker l.toLinearMap)
    have hfA : f ⊆ (A : Set (E n)) := by
      intro z hz
      change z - p₀ ∈ LinearMap.ker l.toLinearMap
      rw [LinearMap.mem_ker]
      simp [hlf z hz, hM]
    have hspan : affineSpan ℝ f ≤ A := (affineSpan_le).2 hfA
    have huA := hspan hu
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker] at huA
    have hzero : l u - l p₀ = 0 := by simpa using huA
    rw [← hM] at hzero
    linarith

  -- Residuo ortogonale di u-p₀ rispetto alla direzione affine di f.
  set S : Submodule ℝ (E n) := vectorSpan ℝ f with hS
  set d : E n := u - p₀ with hd
  set w : E n := d - S.starProjection d with hw
  have hdS : d ∉ S := by
    intro hdmem
    apply huaff
    have hpaff : p₀ ∈ affineSpan ℝ f := mem_affineSpan ℝ hp₀f
    have := vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan hpaff hdmem
    simpa [d] using this
  have hwne : w ≠ 0 := by
    intro hwzero
    have hzero : d - S.starProjection d = 0 := by simpa [w] using hwzero
    have hproj : S.starProjection d = d := (sub_eq_zero.mp hzero).symm
    exact hdS (Submodule.starProjection_eq_self_iff.mp hproj)

  set l₂ : E n →L[ℝ] ℝ := innerSL ℝ w with hl₂
  have hl₂const : ∀ z ∈ f, l₂ z = l₂ p₀ := by
    intro z hz
    have hzS : z - p₀ ∈ S := by
      rw [hS]
      simpa using vsub_mem_vectorSpan ℝ hz hp₀f
    have ho := Submodule.starProjection_inner_eq_zero d (z - p₀) hzS
    change inner ℝ w z = inner ℝ w p₀
    rw [← sub_eq_zero, ← inner_sub_right]
    simpa [w] using ho
  have horth : inner ℝ w (S.starProjection d) = 0 := by
    have hpS : S.starProjection d ∈ S := S.starProjection_apply_mem d
    change inner ℝ (d - S.starProjection d) (S.starProjection d) = 0
    exact Submodule.starProjection_inner_eq_zero d (S.starProjection d) hpS
  have hwd : inner ℝ w d = inner ℝ w w := by
    calc
      inner ℝ w d = inner ℝ w (w + S.starProjection d) := by
        congr 2
        simp [w]
      _ = inner ℝ w w + inner ℝ w (S.starProjection d) :=
        inner_add_right _ _ _
      _ = inner ℝ w w := by rw [horth, add_zero]
  have hl₂gap : l₂ u - l₂ p₀ = ‖w‖ ^ 2 := by
    change inner ℝ w u - inner ℝ w p₀ = ‖w‖ ^ 2
    rw [← inner_sub_right]
    change inner ℝ w d = ‖w‖ ^ 2
    rw [hwd, real_inner_self_eq_norm_sq]
  have hl₂up : l₂ p₀ < l₂ u := by
    have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hwne)
    linarith

  -- Vertici sui quali l₂ cresce e relativi rapporti critici.
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
    obtain ⟨v, hvUp, hvt⟩ := Finset.mem_image.mp (by simpa [hR] using htmem)
    rw [← hvt]
    exact hratio_pos v hvUp

  -- Il funzionale al primo tempo critico.
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

  -- Un vertice realizza il minimo: al tempo t entra nell'argmax.
  have htmem : t ∈ R := by
    rw [ht]
    exact Finset.min'_mem R hRne
  obtain ⟨vcrit, hvcritUp, hvcritEq⟩ :=
    Finset.mem_image.mp (by simpa [hR] using htmem)
  have hvcritV : vcrit ∈ P.vertices := (Finset.mem_filter.mp hvcritUp).1
  have hvcritGrow : l₂ p₀ < l₂ vcrit := (Finset.mem_filter.mp hvcritUp).2
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
    refine ⟨L, ?_⟩
    rfl

  refine ⟨f', hf'face, ?_⟩
  rw [Set.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro hff'
  apply hvcrit_notf
  rw [hff']
  exact hvcritf'

end LeanEval.Geometry.PlatonicClassification

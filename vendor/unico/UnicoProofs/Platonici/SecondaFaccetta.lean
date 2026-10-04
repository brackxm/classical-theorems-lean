import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.SecondoSpigolo

/-!
FASE 3A — LA SECONDA FACCETTA (18 lug 2026).

Il lato «almeno due» del diamante: in un politopo full-dim di ℝ³, ogni
spigolo contenuto in una faccetta A sta anche in una seconda faccetta ≠ A.
Stesso perno esplicito del secondo spigolo, un gradino sopra: w ≠ 0 nel
complemento ortogonale di vectorSpan A, ψ = l_δ + t*·⟪w,·⟫ col rapporto
critico sui vertici del lato buono. ⟪w,·⟫ è costante su A ma l_δ vi morde
(un punto a₁ ∈ A ∖ δ sta strettamente sotto il massimo), quindi un punto
di A dentro l'argmax è assurdo: questo esclude in un colpo solo F = corpo
e F = A. L'argmax contiene δ e il vertice critico fuori dallo span di δ,
quindi ha rango ≥ 2: è la seconda faccetta.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- **LA SECONDA FACCETTA**: in un politopo full-dim di ℝ³ ogni spigolo di
una faccetta sta anche in un'altra faccetta. -/
theorem seconda_faccetta (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {δ : Set (E 3)} (hδ : P.IsFace δ) (hdδ : faceDim δ = 1)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hδA : δ ⊆ A) :
    ∃ A' : Set (E 3), P.IsFace A' ∧ faceDim A' = 2 ∧ δ ⊆ A' ∧ A' ≠ A := by
  classical
  -- l'espositore dello spigolo
  obtain ⟨l, hl⟩ := hδ.1 hδ.2
  obtain ⟨p₀, hp₀δ⟩ := hδ.2
  have hp₀T : p₀ ∈ P.toSet := by
    have := hp₀δ
    rw [hl] at this
    exact this.1
  have hlmax : ∀ y ∈ P.toSet, l y ≤ l p₀ := by
    have := hp₀δ
    rw [hl] at this
    exact this.2
  have hlchar : ∀ q ∈ P.toSet, l q = l p₀ → q ∈ δ := by
    intro q hq hlq
    rw [hl]
    exact ⟨hq, fun y hy => le_trans (hlmax y hy) (le_of_eq hlq.symm)⟩
  have hlconst : ∀ z ∈ δ, l z = l p₀ := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hlmax z hz'.1) (hz'.2 p₀ hp₀T)
  -- il punto di A fuori da δ
  have ha₁ : ∃ a₁ ∈ A, a₁ ∉ δ := by
    by_contra hall
    push_neg at hall
    have hsub : A ⊆ δ := hall
    have hle := vectorSpan_mono ℝ hsub
    have h1 := Submodule.finrank_mono hle
    have h2 : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have h3 : Module.finrank ℝ (vectorSpan ℝ δ) = 1 := hdδ
    omega
  obtain ⟨a₁, ha₁A, ha₁δ⟩ := ha₁
  have ha₁T : a₁ ∈ P.toSet := face_subset_toSet P hA ha₁A
  have ha₁lt : l a₁ < l p₀ := by
    rcases lt_or_eq_of_le (hlmax a₁ ha₁T) with h | h
    · exact h
    · exact absurd (hlchar a₁ ha₁T h) ha₁δ
  -- w non nullo ortogonale allo span della faccetta
  have hwex : ∃ w : E 3, w ∈ (vectorSpan ℝ A)ᗮ ∧ w ≠ 0 := by
    have hsum := Submodule.finrank_add_finrank_orthogonal
      (K := vectorSpan ℝ A)
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have hE : Module.finrank ℝ (E 3) = 3 := by
      rw [finrank_euclideanSpace]
      simp
    have hperp : 1 ≤ Module.finrank ℝ (vectorSpan ℝ A)ᗮ := by omega
    have hne : (vectorSpan ℝ A)ᗮ ≠ ⊥ := by
      intro h
      rw [h] at hperp
      simp [finrank_bot] at hperp
    obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨w, hwmem, hwne⟩
  obtain ⟨w, hwperp, hwne⟩ := hwex
  -- ⟪w,·⟫ è costante su A
  have hwconstA : ∀ z ∈ A, ∀ z' ∈ A, ⟪w, z⟫ = ⟪w, z'⟫ := by
    intro z hz z' hz'
    have hmem : z - z' ∈ vectorSpan ℝ A := vsub_mem_vectorSpan ℝ hz hz'
    have h1 : ⟪z - z', w⟫ = 0 := by
      have := (Submodule.mem_orthogonal (vectorSpan ℝ A) w).mp hwperp
      exact this (z - z') hmem
    rw [real_inner_comm] at h1
    rw [inner_sub_right] at h1
    linarith
  -- w vive nello span del corpo (full-dim ⟹ tutto)
  have hwW : w ∈ vectorSpan ℝ P.toSet := by
    have htop : vectorSpan ℝ P.toSet = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      rw [h1, finrank_euclideanSpace]
      simp
    rw [htop]
    trivial
  obtain ⟨u₀, hu₀V, hu₀ne⟩ := exists_vertex_inner_ne P hp₀T hwW hwne
  -- costruzione parametrizzata dal segno
  have costruzione : ∀ w' : E 3, (∀ z ∈ A, ∀ z' ∈ A, ⟪w', z⟫ = ⟪w', z'⟫) →
      (∃ u ∈ P.vertices, ⟪w', p₀⟫ < ⟪w', u⟫) →
      ∃ A' : Set (E 3), P.IsFace A' ∧ faceDim A' = 2 ∧ δ ⊆ A' ∧ A' ≠ A := by
    intro w' hw'A hup
    obtain ⟨ux, huxV, huxgt⟩ := hup
    set S : Finset (E 3) := P.vertices.filter (fun u => ⟪w', p₀⟫ < ⟪w', u⟫)
      with hS
    have hSne : S.Nonempty := ⟨ux, Finset.mem_filter.mpr ⟨huxV, huxgt⟩⟩
    set r : E 3 → ℝ := fun u => (l p₀ - l u) / (⟪w', u⟫ - ⟪w', p₀⟫) with hr
    obtain ⟨us, husS, husmin⟩ := S.exists_min_image r hSne
    have husV : us ∈ P.vertices := (Finset.mem_filter.mp husS).1
    have husgt : ⟪w', p₀⟫ < ⟪w', us⟫ := (Finset.mem_filter.mp husS).2
    have husT : us ∈ P.toSet := subset_convexHull ℝ _ husV
    have husδ : us ∉ δ := by
      intro h
      have h1 := hw'A us (hδA h) p₀ (hδA hp₀δ)
      rw [h1] at husgt
      exact lt_irrefl _ husgt
    have huslt : l us < l p₀ := by
      rcases lt_or_eq_of_le (hlmax us husT) with h | h
      · exact h
      · exact absurd (hlchar us husT h) husδ
    set t : ℝ := r us with ht
    have htpos : 0 < t := by
      rw [ht, hr]
      apply div_pos
      · linarith
      · linarith
    set ψ : E 3 →L[ℝ] ℝ := l + t • innerSL ℝ w' with hψ
    have hψval : ∀ y : E 3, ψ y = l y + t * ⟪w', y⟫ := by
      intro y
      rw [hψ]
      simp
    have hvert : ∀ u ∈ P.vertices, ψ u ≤ ψ p₀ := by
      intro u huV
      rw [hψval, hψval]
      by_cases hside : ⟪w', p₀⟫ < ⟪w', u⟫
      · have huS : u ∈ S := Finset.mem_filter.mpr ⟨huV, hside⟩
        have hrle : t ≤ r u := husmin u huS
        have hgap : (0:ℝ) < ⟪w', u⟫ - ⟪w', p₀⟫ := by linarith
        have h1 : t * (⟪w', u⟫ - ⟪w', p₀⟫) ≤ r u * (⟪w', u⟫ - ⟪w', p₀⟫) :=
          mul_le_mul_of_nonneg_right hrle (le_of_lt hgap)
        have h2 : r u * (⟪w', u⟫ - ⟪w', p₀⟫) = l p₀ - l u := by
          show (l p₀ - l u) / (⟪w', u⟫ - ⟪w', p₀⟫) * (⟪w', u⟫ - ⟪w', p₀⟫) =
            l p₀ - l u
          exact div_mul_cancel₀ _ (ne_of_gt hgap)
        nlinarith
      · push_neg at hside
        have h1 : l u ≤ l p₀ := hlmax u (subset_convexHull ℝ _ huV)
        have h2 : t * ⟪w', u⟫ ≤ t * ⟪w', p₀⟫ :=
          mul_le_mul_of_nonneg_left hside (le_of_lt htpos)
        linarith
    have hbody : ∀ y ∈ P.toSet, ψ y ≤ ψ p₀ := by
      intro y hy
      have hconv : Convex ℝ {z : E 3 | ψ z ≤ ψ p₀} := by
        apply convex_halfSpace_le
        exact ψ.toLinearMap.isLinear
      have hsub : (P.vertices : Set (E 3)) ⊆ {z : E 3 | ψ z ≤ ψ p₀} := by
        intro u hu
        exact hvert u (Finset.mem_coe.mp hu)
      exact convexHull_min hsub hconv hy
    -- ψ è costante su δ (entrambi i pezzi lo sono)
    have hψδ : ∀ z ∈ δ, ψ z = ψ p₀ := by
      intro z hz
      rw [hψval, hψval, hlconst z hz, hw'A z (hδA hz) p₀ (hδA hp₀δ)]
    set F : Set (E 3) := {x ∈ P.toSet | ∀ y ∈ P.toSet, ψ y ≤ ψ x} with hF
    have hδF : δ ⊆ F := by
      intro z hz
      refine ⟨face_subset_toSet P hδ hz, ?_⟩
      intro y hy
      rw [hψδ z hz]
      exact hbody y hy
    have hp₀F : p₀ ∈ F := hδF hp₀δ
    have hFface : P.IsFace F := ⟨fun _ => ⟨ψ, rfl⟩, ⟨p₀, hp₀F⟩⟩
    -- il vertice critico è in F
    have htie : ψ us = ψ p₀ := by
      rw [hψval, hψval]
      have hgap : (0:ℝ) < ⟪w', us⟫ - ⟪w', p₀⟫ := by linarith
      have h2 : t * (⟪w', us⟫ - ⟪w', p₀⟫) = l p₀ - l us := by
        show (l p₀ - l us) / (⟪w', us⟫ - ⟪w', p₀⟫) * (⟪w', us⟫ - ⟪w', p₀⟫) =
          l p₀ - l us
        exact div_mul_cancel₀ _ (ne_of_gt hgap)
      nlinarith [h2]
    have husF : us ∈ F := by
      refine ⟨husT, ?_⟩
      intro y hy
      rw [htie]
      exact hbody y hy
    -- il punto a₁ di A non può stare in F
    have ha₁F : a₁ ∉ F := by
      intro hmem
      have h1 : ψ a₁ = ψ p₀ :=
        le_antisymm (hbody a₁ ha₁T) (hmem.2 p₀ hp₀T)
      rw [hψval, hψval] at h1
      have h2 : ⟪w', a₁⟫ = ⟪w', p₀⟫ := hw'A a₁ ha₁A p₀ (hδA hp₀δ)
      have h4 : l a₁ = l p₀ := by
        rw [h2] at h1
        linarith
      exact ha₁δ (hlchar a₁ ha₁T h4)
    have hFneT : F ≠ P.toSet := by
      intro h
      exact ha₁F (h ▸ ha₁T)
    have hFneA : F ≠ A := by
      intro h
      exact ha₁F (h ▸ ha₁A)
    -- l è costante sullo span affine di δ
    have hconstspan : ∀ y ∈ affineSpan ℝ δ, l y = l p₀ := by
      intro y hy
      have heqon : Set.EqOn (⇑l.toLinearMap.toAffineMap)
          (⇑(AffineMap.const ℝ (E 3) (l p₀))) δ := by
        intro z hz
        simp [hlconst z hz]
      have h2 := AffineMap.eqOn_affineSpan (k := ℝ) heqon
      have := h2 hy
      simpa using this
    -- il secondo punto di δ e l'indipendenza dei due spostamenti
    obtain ⟨z₁, hz₁δ, hz₁p₀⟩ := faccia_ha_secondo_punto hdδ (v := p₀)
    have hLI : LinearIndependent ℝ ![us - p₀, z₁ - p₀] := by
      rw [linearIndependent_fin2]
      constructor
      · show z₁ - p₀ ≠ 0
        exact sub_ne_zero.mpr hz₁p₀
      · intro a
        show a • (z₁ - p₀) ≠ us - p₀
        intro heq
        have hmem : us ∈ affineSpan ℝ δ := by
          have h1 : a • (z₁ -ᵥ p₀) +ᵥ p₀ ∈ affineSpan ℝ δ :=
            AffineSubspace.smul_vsub_vadd_mem _ a
              (subset_affineSpan ℝ _ hz₁δ)
              (subset_affineSpan ℝ _ hp₀δ)
              (subset_affineSpan ℝ _ hp₀δ)
          have h2 : a • (z₁ -ᵥ p₀) +ᵥ p₀ = us := by
            have h3 : us - p₀ = a • (z₁ - p₀) := heq.symm
            have h4 : us = a • (z₁ - p₀) + p₀ := by
              have := congrArg (fun q => q + p₀) h3
              simpa using this
            rw [h4]
            rfl
          rw [h2] at h1
          exact h1
        have h5 : l us = l p₀ := hconstspan us hmem
        exact husδ (hlchar us husT h5)
    -- rango ≥ 2 per F
    have hsl : Submodule.span ℝ (Set.range ![us - p₀, z₁ - p₀]) ≤
        vectorSpan ℝ F := by
      rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with ⟨iv, hi⟩
      interval_cases iv
      · show (![us - p₀, z₁ - p₀] : Fin 2 → E 3) 0 ∈ vectorSpan ℝ F
        show us - p₀ ∈ vectorSpan ℝ F
        exact vsub_mem_vectorSpan ℝ husF hp₀F
      · show (![us - p₀, z₁ - p₀] : Fin 2 → E 3) 1 ∈ vectorSpan ℝ F
        show z₁ - p₀ ∈ vectorSpan ℝ F
        exact vsub_mem_vectorSpan ℝ (hδF hz₁δ) hp₀F
    have hd2le : 2 ≤ Module.finrank ℝ (vectorSpan ℝ F) := by
      have h1 : Module.finrank ℝ (Submodule.span ℝ
          (Set.range ![us - p₀, z₁ - p₀])) = 2 := by
        rw [finrank_span_eq_card hLI]
        simp
      have h2 := Submodule.finrank_mono hsl
      omega
    have hdlt : Module.finrank ℝ (vectorSpan ℝ F) < 3 := by
      have hss : F ⊂ P.toSet :=
        ⟨fun x hx => hx.1, fun hsup => hFneT
          (Set.Subset.antisymm (fun x hx => hx.1) hsup)⟩
      have h1 := faceDim_lt_of_ssubset P hFface (toSet_isFace P) hss
      have h2 : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
      have h3 : Module.finrank ℝ (vectorSpan ℝ F) <
          Module.finrank ℝ (vectorSpan ℝ P.toSet) := h1
      omega
    refine ⟨F, hFface, ?_, hδF, hFneA⟩
    show Module.finrank ℝ (vectorSpan ℝ F) = 2
    omega
  -- il segno giusto
  rcases lt_or_gt_of_ne hu₀ne with hlt | hgt
  · apply costruzione (-w)
    · intro z hz z' hz'
      rw [inner_neg_left, inner_neg_left, hwconstA z hz z' hz']
    · refine ⟨u₀, hu₀V, ?_⟩
      rw [inner_neg_left, inner_neg_left]
      linarith
  · exact costruzione w hwconstA ⟨u₀, hu₀V, hgt⟩

end LeanEval.Geometry.PlatonicClassification

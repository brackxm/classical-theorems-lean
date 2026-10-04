import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SecondoSpigolo
import UnicoProofs.Platonici.SecondaFaccetta
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.ConoVertice
import UnicoProofs.Platonici.PassoFan

/-!
FASE 3A, F5a — IMMAGINI SOTTO SIMMETRIA E LE TRE FACCETTE (18 lug 2026).

I lemmi d'immagine (una simmetria trasporta facce in facce preservando la
dimensione, il gruppo delle simmetrie è chiuso per identità, composizione
e inversa) ristabiliti in forma pulita fuori dai namespace locali della
fase 2. In coda: due spigoli distinti per v hanno direzioni indipendenti,
quindi due faccette distinte non possono condividerli entrambi; ne segue
che ogni vertice di un politopo full-dim di ℝ³ sta in almeno TRE faccette.
-/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Le esposizioni si trasportano lungo le isometrie affini. -/
theorem isExposed_image_isom (φ : Isom 3) {A B : Set (E 3)}
    (h : IsExposed ℝ A B) : IsExposed ℝ ((⇑φ) '' A) ((⇑φ) '' B) := by
  intro hne
  obtain ⟨b, hbB⟩ := hne
  obtain ⟨a, haB, hab⟩ := hbB
  obtain ⟨l, hl⟩ := h ⟨a, haB⟩
  let l' : E 3 →L[ℝ] ℝ :=
    l.comp φ.symm.linearIsometryEquiv.toLinearIsometry.toContinuousLinearMap
  have hl' (x : E 3) : l' (φ x) = l x - l (φ.symm 0) := by
    have hm := φ.symm.map_vsub (φ x) 0
    have hm' : φ.symm.linearIsometryEquiv (φ x) = x - φ.symm 0 := by
      simpa using hm
    simp only [l', ContinuousLinearMap.comp_apply]
    change l (φ.symm.linearIsometryEquiv (φ x)) = _
    rw [hm', map_sub]
  refine ⟨l', Set.ext ?_⟩
  intro x
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [hl] at hb
    refine ⟨⟨b, hb.1, rfl⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rw [hl' y, hl' b]
    exact sub_le_sub_right (hb.2 y hy) _
  · rintro ⟨hxA, hxmax⟩
    obtain ⟨a, ha, rfl⟩ := hxA
    refine ⟨a, ?_, rfl⟩
    rw [hl]
    refine ⟨ha, ?_⟩
    intro y hy
    have hle := hxmax (φ y) ⟨y, hy, rfl⟩
    rw [hl' y, hl' a] at hle
    linarith

/-- Le isometrie affini preservano la dimensione delle facce. -/
theorem faceDim_image_isom (φ : Isom 3) (F : Set (E 3)) :
    faceDim ((⇑φ) '' F) = faceDim F := by
  unfold ConvexPolytope.faceDim
  have hmap := φ.toAffineEquiv.toAffineMap.map_vectorSpan (s := F)
  change Submodule.map (φ.toAffineEquiv.linear : E 3 →ₗ[ℝ] E 3)
    (vectorSpan ℝ F) = vectorSpan ℝ ((⇑φ) '' F) at hmap
  rw [← hmap]
  exact φ.toAffineEquiv.linear.finrank_map_eq (vectorSpan ℝ F)

/-- Una simmetria trasporta facce in facce. -/
theorem isFace_image_isom {P : ConvexPolytope 3} (φ : Isom 3)
    (hφ : P.isSymmetry φ) {F : Set (E 3)} (hF : P.IsFace F) :
    P.IsFace ((⇑φ) '' F) := by
  refine ⟨?_, hF.2.image _⟩
  rw [← hφ]
  exact isExposed_image_isom φ hF.1

/-- L'identità è una simmetria. -/
theorem symmetry_refl (P : ConvexPolytope 3) :
    P.isSymmetry (AffineIsometryEquiv.refl ℝ (E 3)) := by
  exact Set.image_id _

/-- Le simmetrie sono chiuse per composizione. -/
theorem symmetry_trans {P : ConvexPolytope 3} {φ ψ : Isom 3}
    (hφ : P.isSymmetry φ) (hψ : P.isSymmetry ψ) :
    P.isSymmetry (φ.trans ψ) := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑(φ.trans ψ)) '' P.toSet = (⇑ψ) '' ((⇑φ) '' P.toSet) := by
      rw [Set.image_image]
      rfl
    _ = P.toSet := by rw [hφ, hψ]

/-- Le simmetrie sono chiuse per inversa. -/
theorem symmetry_symm {P : ConvexPolytope 3} {φ : Isom 3}
    (hφ : P.isSymmetry φ) : P.isSymmetry φ.symm := by
  unfold ConvexPolytope.isSymmetry at *
  calc
    (⇑φ.symm) '' P.toSet = (⇑φ.symm) '' ((⇑φ) '' P.toSet) := by rw [hφ]
    _ = P.toSet := φ.toEquiv.symm_image_image P.toSet

/-- Due spigoli distinti per lo stesso punto hanno direzioni indipendenti:
una faccia di rango ≤ 1 non può contenerli entrambi. -/
theorem due_spigoli_non_in_rango_uno (P : ConvexPolytope 3)
    {e₁ e₂ : Set (E 3)} (he₁ : P.IsFace e₁) (hde₁ : faceDim e₁ = 1)
    (he₂ : P.IsFace e₂) (hde₂ : faceDim e₂ = 1) (hne : e₁ ≠ e₂)
    {v : E 3} (hv₁ : v ∈ e₁) (hv₂ : v ∈ e₂)
    {g : Set (E 3)} (hsub₁ : e₁ ⊆ g) (hsub₂ : e₂ ⊆ g)
    (hg : Module.finrank ℝ (vectorSpan ℝ g) ≤ 1) : False := by
  classical
  -- punti secondi
  obtain ⟨a, hae, hav⟩ := faccia_ha_secondo_punto hde₁ (v := v)
  obtain ⟨b, hbe, hbv⟩ := faccia_ha_secondo_punto hde₂ (v := v)
  -- b non sta in e₁ (altrimenti e₁ ∩ e₂ avrebbe rango ≥ 1)
  have hfuori : b ∉ e₁ := by
    intro hbe₁
    have hint : P.IsFace (e₁ ∩ e₂) := ⟨he₁.1.inter he₂.1, ⟨v, hv₁, hv₂⟩⟩
    have hssub : e₁ ∩ e₂ ⊂ e₁ := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have h12 : e₁ ⊆ e₂ := fun z hz => (hsup hz).2
      have hss : e₁ ⊂ e₂ := ⟨h12, fun h => hne (Set.Subset.antisymm h12 h)⟩
      have := faceDim_lt_of_ssubset P he₁ he₂ hss
      omega
    have hlt := faceDim_lt_of_ssubset P hint he₁ hssub
    have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) :=
      finrank_pos_di_due ⟨hv₁, hv₂⟩ ⟨hbe₁, hbe⟩ hbv
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) < 1 := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ (e₁ ∩ e₂)) <
          Module.finrank ℝ (vectorSpan ℝ e₁) := hlt
      have h2 : Module.finrank ℝ (vectorSpan ℝ e₁) = 1 := hde₁
      omega
    omega
  -- l'espositore di e₁ separa: b − v non è multiplo di a − v
  obtain ⟨l₁, hmem₁, hmax₁⟩ := espositore_di_faccia P he₁
  have hl₁a : l₁ a = l₁ v := by
    exact le_antisymm ((hmem₁ v hv₁).2 a (hmem₁ a hae).1)
      ((hmem₁ a hae).2 v (hmem₁ v hv₁).1)
  have hl₁b : l₁ b < l₁ v := by
    have hbT : b ∈ P.toSet := face_subset_toSet P he₂ hbe
    rcases lt_or_eq_of_le ((hmem₁ v hv₁).2 b hbT) with h | h
    · exact h
    · exact absurd (hmax₁ b hbT
        (fun z hz => le_trans ((hmem₁ v hv₁).2 z hz) (le_of_eq h.symm)))
        hfuori
  have hLI : LinearIndependent ℝ ![b - v, a - v] := by
    rw [linearIndependent_fin2]
    constructor
    · show a - v ≠ 0
      exact sub_ne_zero.mpr hav
    · intro c
      show c • (a - v) ≠ b - v
      intro heq
      have hval : l₁ (b - v) = c * (l₁ (a - v)) := by
        rw [← heq, map_smul, smul_eq_mul]
      rw [map_sub, map_sub, hl₁a] at hval
      simp at hval
      linarith
  -- ma entrambe le direzioni stanno nello span di g, di rango ≤ 1
  have hsl : Submodule.span ℝ (Set.range ![b - v, a - v]) ≤
      vectorSpan ℝ g := by
    rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · show (![b - v, a - v] : Fin 2 → E 3) 0 ∈ vectorSpan ℝ g
      show b - v ∈ vectorSpan ℝ g
      exact vsub_mem_vectorSpan ℝ (hsub₂ hbe) (hsub₁ hv₁)
    · show (![b - v, a - v] : Fin 2 → E 3) 1 ∈ vectorSpan ℝ g
      show a - v ∈ vectorSpan ℝ g
      exact vsub_mem_vectorSpan ℝ (hsub₁ hae) (hsub₁ hv₁)
  have h1 : Module.finrank ℝ (Submodule.span ℝ
      (Set.range ![b - v, a - v])) = 2 := by
    rw [finrank_span_eq_card hLI]
    simp
  have h2 := Submodule.finrank_mono hsl
  omega

/-- **TRE FACCETTE AL VERTICE**: in un politopo full-dim di ℝ³ ogni vertice
sta in almeno tre faccette a due a due distinte. -/
theorem tre_faccette_al_vertice (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ A B C : Set (E 3),
      (P.IsFace A ∧ faceDim A = 2 ∧ v ∈ A) ∧
      (P.IsFace B ∧ faceDim B = 2 ∧ v ∈ B) ∧
      (P.IsFace C ∧ faceDim C = 2 ∧ v ∈ C) ∧
      A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  classical
  obtain ⟨F, hF0⟩ := bandiera_al_vertice P hfull hv
  have hA : P.IsFace (F.face 2) := F.isFace 2
  have hdA : faceDim (F.face 2) = 2 := F.dim_eq 2
  have hv1 : v ∈ F.face 1 := (F.strict_mono 0 1 (by decide)).subset
    (hF0 ▸ rfl)
  have hv2 : v ∈ F.face 2 := (F.strict_mono 1 2 (by decide)).subset hv1
  have hε₁ : P.IsFace (F.face 1) := F.isFace 1
  have hdε₁ : faceDim (F.face 1) = 1 := F.dim_eq 1
  have hε₁A : F.face 1 ⊆ F.face 2 := (F.strict_mono 1 2 (by decide)).subset
  -- il passo del fan: A₂ ≠ A col nuovo spigolo δ
  obtain ⟨G, L, R, hG0, hL0, hL2, hR2, hLR, hGne, hLne, _⟩ :=
    passo_del_fan P hfull hv F hF0
  have hA₂ : P.IsFace (G.face 2) := G.isFace 2
  have hdA₂ : faceDim (G.face 2) = 2 := G.dim_eq 2
  have hvG2 : v ∈ G.face 2 := by
    have h1 : v ∈ G.face 1 := (G.strict_mono 0 1 (by decide)).subset
      (hG0 ▸ rfl)
    exact (G.strict_mono 1 2 (by decide)).subset h1
  -- lo spigolo δ = L.face 1 sta in entrambe
  have hδ : P.IsFace (L.face 1) := L.isFace 1
  have hdδ : faceDim (L.face 1) = 1 := L.dim_eq 1
  have hvδ : v ∈ L.face 1 := (L.strict_mono 0 1 (by decide)).subset
    (hL0 ▸ rfl)
  have hδA : L.face 1 ⊆ F.face 2 := by
    have h1 : L.face 1 ⊆ L.face 2 := (L.strict_mono 1 2 (by decide)).subset
    rwa [hL2] at h1
  have hδA₂ : L.face 1 ⊆ G.face 2 := by
    have h1 : R.face 1 ⊆ R.face 2 := (R.strict_mono 1 2 (by decide)).subset
    rw [hR2] at h1
    rwa [← hLR] at h1
  -- la seconda faccetta per ε₁
  obtain ⟨A₀, hA₀, hdA₀, hε₁A₀, hA₀ne⟩ := seconda_faccetta P hfull hε₁ hdε₁
    hA hdA hε₁A
  have hvA₀ : v ∈ A₀ := hε₁A₀ hv1
  -- A₀ ≠ A₂: altrimenti A e A₂ condividerebbero due spigoli distinti
  have hA₀A₂ : A₀ ≠ G.face 2 := by
    intro h
    -- ε₁ ⊆ A₀ = A₂ e δ ⊆ A₂; ε₁, δ ⊆ A ∩ A₂ con rango ≤ 1
    have hint : P.IsFace (F.face 2 ∩ G.face 2) :=
      ⟨hA.1.inter hA₂.1, ⟨v, hv2, hvG2⟩⟩
    have hssub : F.face 2 ∩ G.face 2 ⊂ F.face 2 := by
      refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
      have h12 : F.face 2 ⊆ G.face 2 := fun z hz => (hsup hz).2
      have hss : F.face 2 ⊂ G.face 2 :=
        ⟨h12, fun h' => hGne (Set.Subset.antisymm h' h12)⟩
      have := faceDim_lt_of_ssubset P hA hA₂ hss
      omega
    have hlt := faceDim_lt_of_ssubset P hint hA hssub
    have hrk : Module.finrank ℝ (vectorSpan ℝ (F.face 2 ∩ G.face 2)) ≤ 1 := by
      have h1 : Module.finrank ℝ (vectorSpan ℝ (F.face 2 ∩ G.face 2)) <
          Module.finrank ℝ (vectorSpan ℝ (F.face 2)) := hlt
      have h2 : Module.finrank ℝ (vectorSpan ℝ (F.face 2)) = 2 := hdA
      omega
    apply due_spigoli_non_in_rango_uno P hε₁ hdε₁ hδ hdδ
      (Ne.symm hLne) hv1 hvδ (g := F.face 2 ∩ G.face 2) ?_ ?_ hrk
    · intro z hz
      refine ⟨hε₁A hz, ?_⟩
      rw [← h]
      exact hε₁A₀ hz
    · intro z hz
      exact ⟨hδA hz, hδA₂ hz⟩
  exact ⟨F.face 2, G.face 2, A₀,
    ⟨hA, hdA, hv2⟩, ⟨hA₂, hdA₂, hvG2⟩, ⟨hA₀, hdA₀, hvA₀⟩,
    hGne.symm, Ne.symm hA₀ne, Ne.symm hA₀A₂⟩

end LeanEval.Geometry.PlatonicClassification

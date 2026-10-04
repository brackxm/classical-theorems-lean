/- Modified for the ClassicalTheorems project by Codex on 2026-10-02:
   compatibility updates for Lean 4.34.0 and the pinned mathlib revision. -/

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.VerticiEsposti
import UnicoProofs.Platonici.SottoPolitopo
import UnicoProofs.Platonici.DimStretta
import UnicoProofs.Platonici.DueFunzionali
import UnicoProofs.Platonici.Perno
import UnicoProofs.Platonici.Interpolazione
import UnicoProofs.Platonici.ScalaBandiere
import UnicoProofs.Platonici.BandieraCompagna
import UnicoProofs.Platonici.Diamante
import UnicoProofs.Platonici.Diamante2D
import UnicoProofs.Platonici.SecondoSpigolo
import UnicoProofs.Platonici.SecondaFaccetta
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.ConoVertice
import UnicoProofs.Platonici.Camminata
import UnicoProofs.Platonici.ScaricoSpigolo

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

/-- Due faccette per v condividono uno spigolo per v. -/
def SpigoloComune (P : ConvexPolytope 3) (v : E 3) (A B : Set (E 3)) : Prop :=
  ∃ δ : Set (E 3), P.IsFace δ ∧ faceDim δ = 1 ∧ v ∈ δ ∧ δ ⊆ A ∧ δ ⊆ B

/-- Gli spigoli del politopo che passano per `v`, come tipo finito. -/
def SpigoloPer (P : ConvexPolytope 3) (v : E 3) :=
  {e : Set (E 3) // P.IsFace e ∧ faceDim e = 1 ∧ v ∈ e}

namespace SpigoloPer

variable (P : ConvexPolytope 3) (v : E 3)

instance : DecidableEq (SpigoloPer P v) := Classical.decEq _

/-- Il secondo estremo, scelto una volta per tutte. -/
noncomputable def altro (hv : v ∈ P.vertices) (e : SpigoloPer P v) : E 3 :=
  Classical.choose (spigolo_segmento P e.property.1 e.property.2.1 hv e.property.2.2)

theorem altro_spec (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    altro P v hv e ∈ P.vertices ∧ altro P v hv e ∈ e.val ∧
      altro P v hv e ≠ v ∧
      e.val = segment ℝ v (altro P v hv e) :=
  Classical.choose_spec
    (spigolo_segmento P e.property.1 e.property.2.1 hv e.property.2.2)

/-- Punto in cui lo spigolo taglia il livello `l = c`. -/
noncomputable def taglio (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ)
    (e : SpigoloPer P v) : E 3 :=
  v + ((l v - c) / (l v - l (altro P v hv e))) • (altro P v hv e - v)

theorem taglio_fatti (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ)
    (hc : c < l v) (e : SpigoloPer P v)
    (ha : l (altro P v hv e) < c) :
    taglio P v hv l c e ∈ e.val ∧
      l (taglio P v hv l c e) = c ∧
      e.val ∩ {y | l y = c} = {taglio P v hv l c e} := by
  classical
  let a : E 3 := altro P v hv e
  let θ : ℝ := (l v - c) / (l v - l a)
  have hden : 0 < l v - l a := by linarith
  have hnum : 0 < l v - c := by linarith
  have hθ0 : 0 < θ := by
    exact div_pos hnum hden
  have hθ1 : θ < 1 := by
    rw [div_lt_one hden]
    linarith
  have hseg : e.val = segment ℝ v a := (altro_spec P v hv e).2.2.2
  have hxform : taglio P v hv l c e = v + θ • (a - v) := rfl
  have hxseg : taglio P v hv l c e ∈ e.val := by
    rw [hseg, hxform]
    refine ⟨1 - θ, θ, by linarith, le_of_lt hθ0, by ring, ?_⟩
    match_scalars <;> ring
  have hxlevel : l (taglio P v hv l c e) = c := by
    rw [hxform]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hdenne : l v - l a ≠ 0 := ne_of_gt hden
    have hcancel : (l v - c) / (l v - l a) * (l v - l a) = l v - c :=
      div_mul_cancel₀ _ hdenne
    nlinarith
  refine ⟨hxseg, hxlevel, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    have hye : y ∈ segment ℝ v a := by simpa [hseg] using hy.1
    rcases hye with ⟨r, s, hr, hs, hrs, hyform⟩
    have hylevel : l y = c := hy.2
    have hsθ : s = θ := by
      rw [← hyform] at hylevel
      simp only [map_add, map_smul, smul_eq_mul] at hylevel
      have hrform : r = 1 - s := by linarith
      rw [hrform] at hylevel
      have heq : s * (l v - l a) = l v - c := by linarith
      apply (eq_div_iff (ne_of_gt hden)).2
      linarith
    have hry : r = 1 - θ := by linarith
    rw [Set.mem_singleton_iff]
    rw [hxform, ← hyform, hsθ, hry]
    match_scalars <;> ring
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨hxseg, hxlevel⟩

end SpigoloPer

/-- Un livello che separa `v` da tutti gli altri vertici. -/
theorem esiste_livello_separatore (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ l : E 3 →L[ℝ] ℝ, ∃ c : ℝ,
      c < l v ∧ ∀ u ∈ P.vertices, u ≠ v → l u < c := by
  classical
  have hvface : P.IsFace ({v} : Set (E 3)) := vertex_isFace P hv
  obtain ⟨l, hlmem, hlchar⟩ := espositore_di_faccia P hvface
  have hvT : v ∈ P.toSet := (hlmem v (Set.mem_singleton v)).1
  have hlmax : ∀ y ∈ P.toSet, l y ≤ l v :=
    (hlmem v (Set.mem_singleton v)).2
  have hlstrict : ∀ u ∈ P.vertices, u ≠ v → l u < l v := by
    intro u huV huv
    have huT : u ∈ P.toSet := subset_convexHull ℝ _ huV
    rcases lt_or_eq_of_le (hlmax u huT) with h | h
    · exact h
    · have huSing : u ∈ ({v} : Set (E 3)) :=
        hlchar u huT (fun z hz => le_trans (hlmax z hz) (le_of_eq h.symm))
      exact (huv (Set.mem_singleton_iff.mp huSing)).elim
  have hsing_ne : ({v} : Set (E 3)) ≠ P.toSet := by
    intro heq
    have hPdim : faceDim P.toSet = 3 := hfull
    rw [← heq, faceDim_singleton] at hPdim
    omega
  obtain ⟨w, hwV, hwne⟩ := exists_vertex_notMem_of_ne_toSet P hvface hsing_ne
  have hwv : w ≠ v := by
    intro h
    subst w
    exact hwne (Set.mem_singleton v)
  let S : Finset (E 3) := P.vertices.erase v
  have hSne : S.Nonempty := ⟨w, Finset.mem_erase.mpr ⟨hwv, hwV⟩⟩
  obtain ⟨m, hmS, hmmax⟩ := S.exists_max_image l hSne
  let c : ℝ := (l v + l m) / 2
  have hmlt : l m < l v := by
    exact hlstrict m (Finset.mem_of_mem_erase hmS) (Finset.ne_of_mem_erase hmS)
  refine ⟨l, c, by dsimp [c]; linarith, ?_⟩
  intro u huV huv
  have huS : u ∈ S := Finset.mem_erase.mpr ⟨huv, huV⟩
  have hule : l u ≤ l m := hmmax u huS
  dsimp [c]
  linarith

/-- In una faccetta, dato uno dei due spigoli per `v`, esiste un unico
altro spigolo per `v`. -/
theorem unico_altro_spigolo_nella_faccetta (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (e : SpigoloPer P v) (heA : e.val ⊆ A) :
    ∃ e' : SpigoloPer P v, e'.val ⊆ A ∧ e' ≠ e ∧
      ∀ d : SpigoloPer P v, d.val ⊆ A → d ≠ e → d = e' := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := by
    exact Finset.mem_filter.mpr ⟨hv, hvA⟩
  have heQ : Q.IsFace e.val := facePolytope_isFace_of P hA e.property.1 heA
  obtain ⟨g, hgQ, hdg, hvg, hgne⟩ :=
    secondo_spigolo Q hQdim hvQ heQ e.property.2.1 e.property.2.2
  have hgP : P.IsFace g := isFace_of_facePolytope P hA hgQ
  have hgA : g ⊆ A := by
    have := face_subset_toSet Q hgQ
    rwa [hQT] at this
  let e' : SpigoloPer P v := ⟨g, hgP, hdg, hvg⟩
  have he'ne : e' ≠ e := by
    intro h
    apply hgne
    exact congrArg Subtype.val h
  refine ⟨e', hgA, he'ne, ?_⟩
  intro d hdA hde
  have hdQ : Q.IsFace d.val := facePolytope_isFace_of P hA d.property.1 hdA
  by_contra hde'
  have he_g : e.val ≠ g := fun h => hgne h.symm
  have he_d : e.val ≠ d.val := fun h => hde (Subtype.ext h.symm)
  have hg_d : g ≠ d.val := fun h => hde' (Subtype.ext h.symm)
  exact diamante_poligono Q hQdim heQ e.property.2.1 hgQ hdg hdQ d.property.2.1
    he_g he_d hg_d e.property.2.2 hvg d.property.2.2

/-- La sezione di una faccetta al livello separatore è il segmento fra gli
attraversamenti dei suoi due spigoli per `v`. -/
theorem sezione_faccetta_segmento (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (e₁ e₂ : SpigoloPer P v) (he₁A : e₁.val ⊆ A) (he₂A : e₂.val ⊆ A)
    (hne : e₁ ≠ e₂)
    (ha₁ : l (SpigoloPer.altro P v hv e₁) < c)
    (ha₂ : l (SpigoloPer.altro P v hv e₂) < c) :
    A ∩ {y | l y = c} =
      segment ℝ (SpigoloPer.taglio P v hv l c e₁)
        (SpigoloPer.taglio P v hv l c e₂) := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv, hvA⟩
  have he₁Q : Q.IsFace e₁.val := facePolytope_isFace_of P hA e₁.property.1 he₁A
  have he₂Q : Q.IsFace e₂.val := facePolytope_isFace_of P hA e₂.property.1 he₂A
  let a : E 3 := SpigoloPer.altro P v hv e₁
  let b : E 3 := SpigoloPer.altro P v hv e₂
  let x₁ : E 3 := SpigoloPer.taglio P v hv l c e₁
  let x₂ : E 3 := SpigoloPer.taglio P v hv l c e₂
  have ha₁e : a ∈ e₁.val := (SpigoloPer.altro_spec P v hv e₁).2.1
  have ha₁v : a ≠ v := (SpigoloPer.altro_spec P v hv e₁).2.2.1
  have hseg₁ : e₁.val = segment ℝ v a :=
    (SpigoloPer.altro_spec P v hv e₁).2.2.2
  have ha₂e : b ∈ e₂.val := (SpigoloPer.altro_spec P v hv e₂).2.1
  have ha₂v : b ≠ v := (SpigoloPer.altro_spec P v hv e₂).2.2.1
  have hseg₂ : e₂.val = segment ℝ v b :=
    (SpigoloPer.altro_spec P v hv e₂).2.2.2
  have hval₁ : l x₁ = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc e₁ ha₁).2.1
  have hval₂ : l x₂ = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc e₂ ha₂).2.1
  have hx₁A : x₁ ∈ A := he₁A
    (SpigoloPer.taglio_fatti P v hv l c hc e₁ ha₁).1
  have hx₂A : x₂ ∈ A := he₂A
    (SpigoloPer.taglio_fatti P v hv l c hc e₂ ha₂).1
  have hneval : e₁.val ≠ e₂.val := fun h => hne (Subtype.ext h)
  apply Set.Subset.antisymm
  · intro y hy
    have hyQ : y ∈ Q.toSet := by
      rw [hQT]
      exact hy.1
    obtain ⟨s, t, hs, ht, hyform⟩ :=
      cono_al_vertice Q hQdim hvQ he₁Q e₁.property.2.1
        he₂Q e₂.property.2.1 hneval ha₁e ha₁v hseg₁
        ha₂e ha₂v hseg₂ e₁.property.2.2 e₂.property.2.2 y hyQ
    have hyval : l y = l v + s * (l a - l v) + t * (l b - l v) := by
      rw [hyform]
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    have hbalance : s * (l v - l a) + t * (l v - l b) = l v - c := by
      have := hy.2
      change l y = c at this
      linarith
    have hD : 0 < l v - c := by linarith
    have hd₁ : 0 < l v - l a := by
      change l a < c at ha₁
      linarith
    have hd₂ : 0 < l v - l b := by
      change l b < c at ha₂
      linarith
    let lam : ℝ := s * (l v - l a) / (l v - c)
    let mu : ℝ := t * (l v - l b) / (l v - c)
    have hlam : 0 ≤ lam := div_nonneg (mul_nonneg hs (le_of_lt hd₁)) (le_of_lt hD)
    have hmu : 0 ≤ mu := div_nonneg (mul_nonneg ht (le_of_lt hd₂)) (le_of_lt hD)
    have hsum : lam + mu = 1 := by
      rw [← add_div]
      rw [hbalance, div_self (ne_of_gt hD)]
    refine ⟨lam, mu, hlam, hmu, hsum, ?_⟩
    change lam • x₁ + mu • x₂ = y
    have hx₁form : x₁ = v + ((l v - c) / (l v - l a)) • (a - v) := rfl
    have hx₂form : x₂ = v + ((l v - c) / (l v - l b)) • (b - v) := rfl
    rw [hx₁form, hx₂form, hyform]
    dsimp [lam, mu]
    match_scalars
    all_goals
      field_simp
      try ring_nf at hbalance ⊢
      try nlinarith [hbalance]
  · intro y hy
    have hyA : y ∈ A :=
      (hA.1.convex (convex_convexHull ℝ _)).segment_subset hx₁A hx₂A hy
    have hylevel : l y = c := by
      rcases hy with ⟨r, s, hr, hs, hrs, hyform⟩
      rw [← hyform]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [hval₁, hval₂]
      rw [← add_mul, hrs, one_mul]
    exact ⟨hyA, hylevel⟩

/-- Due spigoli per lo stesso vertice che hanno un secondo punto comune
coincidono. -/
theorem spigoli_eq_of_punto_comune (P : ConvexPolytope 3) {v x : E 3}
    {e d : Set (E 3)}
    (he : P.IsFace e) (hde : faceDim e = 1) (hve : v ∈ e)
    (hd : P.IsFace d) (hdd : faceDim d = 1) (hvd : v ∈ d)
    (hxe : x ∈ e) (hxd : x ∈ d) (hxv : x ≠ v) : e = d := by
  have hint : P.IsFace (e ∩ d) := ⟨he.1.inter hd.1, ⟨v, hve, hvd⟩⟩
  have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) :=
    finrank_pos_di_due ⟨hve, hvd⟩ ⟨hxe, hxd⟩ hxv
  have heqint : e ∩ d = e := by
    apply Set.Subset.antisymm Set.inter_subset_left
    by_contra hnot
    have hss : e ∩ d ⊂ e := ⟨Set.inter_subset_left, hnot⟩
    have hlt := faceDim_lt_of_ssubset P hint he hss
    have hlt' : Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) < 1 := by
      have hlt0 : Module.finrank ℝ (vectorSpan ℝ (e ∩ d)) <
          Module.finrank ℝ (vectorSpan ℝ e) := hlt
      have hedim : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
      omega
    omega
  have hed : e ⊆ d := by
    intro y hy
    have : y ∈ e ∩ d := by rwa [heqint]
    exact this.2
  apply Set.Subset.antisymm hed
  by_contra hnot
  have hss : e ⊂ d := ⟨hed, hnot⟩
  have hlt := faceDim_lt_of_ssubset P he hd hss
  have hlt' : Module.finrank ℝ (vectorSpan ℝ e) <
      Module.finrank ℝ (vectorSpan ℝ d) := hlt
  have hde' : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
  have hdd' : Module.finrank ℝ (vectorSpan ℝ d) = 1 := hdd
  omega

/-- Due faccette distinte che contengono lo stesso spigolo si intersecano
esattamente in quello spigolo. -/
theorem intersezione_faccette_eq_spigolo (P : ConvexPolytope 3)
    {e A B : Set (E 3)}
    (he : P.IsFace e) (hde : faceDim e = 1)
    (hA : P.IsFace A) (hdA : faceDim A = 2)
    (hB : P.IsFace B) (hdB : faceDim B = 2)
    (heA : e ⊆ A) (heB : e ⊆ B) (hAB : A ≠ B) : A ∩ B = e := by
  obtain ⟨v, hve⟩ := he.2
  have hint : P.IsFace (A ∩ B) := ⟨hA.1.inter hB.1, ⟨v, heA hve, heB hve⟩⟩
  have hintA : A ∩ B ⊂ A := by
    refine ⟨Set.inter_subset_left, fun hsup => ?_⟩
    have hAleB : A ⊆ B := fun x hx => (hsup hx).2
    have hss : A ⊂ B := ⟨hAleB, fun hBA => hAB (Set.Subset.antisymm hAleB hBA)⟩
    have hlt := faceDim_lt_of_ssubset P hA hB hss
    omega
  have hdintlt := faceDim_lt_of_ssubset P hint hA hintA
  have heint : e ⊆ A ∩ B := fun x hx => ⟨heA hx, heB hx⟩
  have hge : 1 ≤ Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) := by
    have hmono := vectorSpan_mono ℝ heint
    have hfin := Submodule.finrank_mono hmono
    have hedim : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    omega
  have hdint : faceDim (A ∩ B) = 1 := by
    show Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1
    have hdA' : Module.finrank ℝ (vectorSpan ℝ A) = 2 := hdA
    have hdintlt' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) < 2 := by
      have hlt0 : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) <
          Module.finrank ℝ (vectorSpan ℝ A) := hdintlt
      omega
    omega
  apply Set.Subset.antisymm
  · by_contra hnot
    have hss : e ⊂ A ∩ B := ⟨heint, hnot⟩
    have hlt := faceDim_lt_of_ssubset P he hint hss
    have hlt' : Module.finrank ℝ (vectorSpan ℝ e) <
        Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) := hlt
    have hde' : Module.finrank ℝ (vectorSpan ℝ e) = 1 := hde
    have hdint' : Module.finrank ℝ (vectorSpan ℝ (A ∩ B)) = 1 := hdint
    omega
  · exact heint

/-- Attraversamenti di spigoli distinti sono distinti. -/
theorem tagli_distinti (P : ConvexPolytope 3) {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (e d : SpigoloPer P v) (hed : e ≠ d)
    (hae : l (SpigoloPer.altro P v hv e) < c)
    (had : l (SpigoloPer.altro P v hv d) < c) :
    SpigoloPer.taglio P v hv l c e ≠ SpigoloPer.taglio P v hv l c d := by
  intro h
  let x := SpigoloPer.taglio P v hv l c e
  have hxe : x ∈ e.val := (SpigoloPer.taglio_fatti P v hv l c hc e hae).1
  have hxd : x ∈ d.val := by
    change SpigoloPer.taglio P v hv l c e ∈ d.val
    rw [h]
    exact (SpigoloPer.taglio_fatti P v hv l c hc d had).1
  have hxv : x ≠ v := by
    intro hx
    have hxlevel := (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.1
    change l x = c at hxlevel
    rw [hx] at hxlevel
    linarith
  have heq := spigoli_eq_of_punto_comune P e.property.1 e.property.2.1
    e.property.2.2 d.property.1 d.property.2.1 d.property.2.2 hxe hxd hxv
  exact hed (Subtype.ext heq)

/-- Il cono della sezione nel punto che attraversa uno spigolo comune a due
faccette. Le due direzioni sono quelle verso gli altri spigoli delle due
faccette. -/
theorem cono_al_taglio (P : ConvexPolytope 3) {v : E 3} (hv : v ∈ P.vertices)
    (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (hvert : ∀ u ∈ P.vertices, u ≠ v → l u < c)
    (e eA eB : SpigoloPer P v)
    {A B : Set (E 3)}
    (hA : P.IsFace A) (hdA : faceDim A = 2) (_hvA : v ∈ A)
    (hB : P.IsFace B) (hdB : faceDim B = 2) (_hvB : v ∈ B)
    (heA : e.val ⊆ A) (heB : e.val ⊆ B) (hAB : A ≠ B)
    (heAA : eA.val ⊆ A) (heBB : eB.val ⊆ B)
    (heAne : eA ≠ e) (heBne : eB ≠ e) :
    ∀ z ∈ P.toSet ∩ {q | l q = c},
      ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧
        z = SpigoloPer.taglio P v hv l c e +
          s • (SpigoloPer.taglio P v hv l c eA -
            SpigoloPer.taglio P v hv l c e) +
          t • (SpigoloPer.taglio P v hv l c eB -
            SpigoloPer.taglio P v hv l c e) := by
  classical
  let x : E 3 := SpigoloPer.taglio P v hv l c e
  let yA : E 3 := SpigoloPer.taglio P v hv l c eA
  let yB : E 3 := SpigoloPer.taglio P v hv l c eB
  have hae : l (SpigoloPer.altro P v hv e) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv e).1
      (SpigoloPer.altro_spec P v hv e).2.2.1
  have haA : l (SpigoloPer.altro P v hv eA) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv eA).1
      (SpigoloPer.altro_spec P v hv eA).2.2.1
  have haB : l (SpigoloPer.altro P v hv eB) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv eB).1
      (SpigoloPer.altro_spec P v hv eB).2.2.1
  have hxe : x ∈ e.val := (SpigoloPer.taglio_fatti P v hv l c hc e hae).1
  have hyAeA : yA ∈ eA.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc eA haA).1
  have hyBeB : yB ∈ eB.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc eB haB).1
  have hxval : l x = c := (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.1
  have hyAval : l yA = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc eA haA).2.1
  have hyBval : l yB = c :=
    (SpigoloPer.taglio_fatti P v hv l c hc eB haB).2.1
  have hxA : x ∈ A := heA hxe
  have hxB : x ∈ B := heB hxe
  have hyAA : yA ∈ A := heAA hyAeA
  have hyBB : yB ∈ B := heBB hyBeB
  have hyAne : yA ≠ x :=
    tagli_distinti P hv l c hc eA e heAne haA hae
  have hyBne : yB ≠ x :=
    tagli_distinti P hv l c hc eB e heBne haB hae
  have hint : A ∩ B = e.val :=
    intersezione_faccette_eq_spigolo P e.property.1 e.property.2.1
      hA hdA hB hdB heA heB hAB
  have hyBnotA : yB ∉ A := by
    intro hyBA
    have hyBe : yB ∈ e.val := by
      rw [← hint]
      exact ⟨hyBA, hyBB⟩
    have hyBsing : yB ∈ ({x} : Set (E 3)) := by
      rw [← (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.2]
      exact ⟨hyBe, hyBval⟩
    exact hyBne (Set.mem_singleton_iff.mp hyBsing)
  have hyAnotB : yA ∉ B := by
    intro hyAB
    have hyAe : yA ∈ e.val := by
      rw [← hint]
      exact ⟨hyAA, hyAB⟩
    have hyAsing : yA ∈ ({x} : Set (E 3)) := by
      rw [← (SpigoloPer.taglio_fatti P v hv l c hc e hae).2.2]
      exact ⟨hyAe, hyAval⟩
    exact hyAne (Set.mem_singleton_iff.mp hyAsing)
  obtain ⟨lA, hmemA, hcharA⟩ := espositore_di_faccia P hA
  obtain ⟨lB, hmemB, hcharB⟩ := espositore_di_faccia P hB
  have hAx : ∀ z ∈ P.toSet, lA z ≤ lA x := (hmemA x hxA).2
  have hBx : ∀ z ∈ P.toSet, lB z ≤ lB x := (hmemB x hxB).2
  have hAyA : lA yA = lA x := by
    exact le_antisymm ((hmemA x hxA).2 yA (hmemA yA hyAA).1)
      ((hmemA yA hyAA).2 x (hmemA x hxA).1)
  have hByB : lB yB = lB x := by
    exact le_antisymm ((hmemB x hxB).2 yB (hmemB yB hyBB).1)
      ((hmemB yB hyBB).2 x (hmemB x hxB).1)
  have hAyB : lA yB < lA x := by
    rcases lt_or_eq_of_le (hAx yB (hmemB yB hyBB).1) with h | h
    · exact h
    · have : yB ∈ A := hcharA yB (hmemB yB hyBB).1
          (fun z hz => le_trans (hAx z hz) (le_of_eq h.symm))
      exact (hyBnotA this).elim
  have hByA : lB yA < lB x := by
    rcases lt_or_eq_of_le (hBx yA (hmemA yA hyAA).1) with h | h
    · exact h
    · have : yA ∈ B := hcharB yA (hmemA yA hyAA).1
          (fun z hz => le_trans (hBx z hz) (le_of_eq h.symm))
      exact (hyAnotB this).elim
  let u : E 3 := yA - x
  let w : E 3 := yB - x
  have hAu : lA u = 0 := by
    dsimp [u]
    simp only [map_sub]
    linarith
  have hAw : lA w < 0 := by
    dsimp [w]
    simp only [map_sub]
    linarith
  have hBu : lB u < 0 := by
    dsimp [u]
    simp only [map_sub]
    linarith
  have hBw : lB w = 0 := by
    dsimp [w]
    simp only [map_sub]
    linarith
  have hLI : LinearIndependent ℝ ![u, w] := by
    rw [linearIndependent_fin2]
    constructor
    · show w ≠ 0
      exact sub_ne_zero.mpr hyBne
    · intro q
      show q • w ≠ u
      intro hq
      have hmap := congrArg lA hq
      simp only [map_smul, smul_eq_mul] at hmap
      rw [hAu] at hmap
      have hq0 : q = 0 := by nlinarith
      rw [hq0, zero_smul] at hq
      exact (sub_ne_zero.mpr hyAne) hq.symm
  let U : Submodule ℝ (E 3) := Submodule.span ℝ (Set.range ![u, w])
  have hUker : U ≤ LinearMap.ker l.toLinearMap := by
    rw [Submodule.span_le]
    rintro q ⟨i, rfl⟩
    rcases i with ⟨iv, hi⟩
    interval_cases iv
    · show l u = 0
      dsimp [u]
      simp only [map_sub]
      linarith
    · show l w = 0
      dsimp [w]
      simp only [map_sub]
      linarith
  have hsurj : Function.Surjective l.toLinearMap := by
    intro r
    refine ⟨(r / (l v - c)) • (v - x), ?_⟩
    change l ((r / (l v - c)) • (v - x)) = r
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [hxval]
    exact div_mul_cancel₀ r (ne_of_gt (by linarith : 0 < l v - c))
  have hrange : Module.finrank ℝ (LinearMap.range l.toLinearMap) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp
  have hker : Module.finrank ℝ (LinearMap.ker l.toLinearMap) = 2 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker l.toLinearMap
    have hE : Module.finrank ℝ (E 3) = 3 := by
      rw [finrank_euclideanSpace]
      simp
    omega
  have hUdim : Module.finrank ℝ U = 2 := by
    dsimp [U]
    rw [finrank_span_eq_card hLI]
    simp
  have hUeq : U = LinearMap.ker l.toLinearMap := by
    apply Submodule.eq_of_le_of_finrank_le hUker
    omega
  intro z hz
  have hzker : z - x ∈ LinearMap.ker l.toLinearMap := by
    change l (z - x) = 0
    simp only [map_sub]
    have hzval : l z = c := hz.2
    linarith
  rw [← hUeq] at hzker
  obtain ⟨coef, hcoef⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (R := ℝ)).mp hzker
  rw [Fin.sum_univ_two] at hcoef
  have hcoef' : coef 0 • u + coef 1 • w = z - x := hcoef
  have hzform : z = x + coef 0 • u + coef 1 • w := by
    have h := congrArg (fun q => q + x) hcoef'
    simp at h
    rw [← h]
    abel
  have hAz : lA z = lA x + coef 1 * lA w := by
    rw [hzform]
    simp only [map_add, map_smul, smul_eq_mul, hAu, mul_zero, add_zero]
  have hBz : lB z = lB x + coef 0 * lB u := by
    rw [hzform]
    simp only [map_add, map_smul, smul_eq_mul, hBw, mul_zero, add_zero]
  have ht : 0 ≤ coef 1 := by
    have hmax := hAx z hz.1
    rw [hAz] at hmax
    by_contra hneg
    push Not at hneg
    nlinarith
  have hs : 0 ≤ coef 0 := by
    have hmax := hBx z hz.1
    rw [hBz] at hmax
    by_contra hneg
    push Not at hneg
    nlinarith
  exact ⟨coef 0, coef 1, hs, ht, hzform⟩

/-- Le due faccette di uno spigolo e, in ciascuna, l'altro spigolo per `v`. -/
structure StellaSpigolo (P : ConvexPolytope 3) (v : E 3)
    (e : SpigoloPer P v) where
  A : Set (E 3)
  B : Set (E 3)
  hA : P.IsFace A
  hdA : faceDim A = 2
  hB : P.IsFace B
  hdB : faceDim B = 2
  heA : e.val ⊆ A
  heB : e.val ⊆ B
  hAB : A ≠ B
  eA : SpigoloPer P v
  eB : SpigoloPer P v
  heAA : eA.val ⊆ A
  heBB : eB.val ⊆ B
  heAne : eA ≠ e
  heBne : eB ≠ e

/-- Ogni spigolo per un vertice di un politopo 3D full-dimensional ha una
stella completa. -/
theorem stella_spigolo_esiste (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    Nonempty (StellaSpigolo P v e) := by
  classical
  have hPdim : Module.finrank ℝ (vectorSpan ℝ P.toSet) = 3 := hfull
  have hgap : faceDim e.val + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ P.toSet) := by
    rw [e.property.2.1, hPdim]
  obtain ⟨A, hA, heAss, hAne⟩ := interpolazione P e.property.1 hgap
  have heA : e.val ⊆ A := heAss.subset
  have hdA : faceDim A = 2 := by
    show Module.finrank ℝ (vectorSpan ℝ A) = 2
    have hlo0 := faceDim_lt_of_ssubset P e.property.1 hA heAss
    have hlo : Module.finrank ℝ (vectorSpan ℝ e.val) <
        Module.finrank ℝ (vectorSpan ℝ A) := hlo0
    have hedim : Module.finrank ℝ (vectorSpan ℝ e.val) = 1 := e.property.2.1
    have hAss : A ⊂ P.toSet :=
      ⟨face_subset_toSet P hA, fun hsub =>
        hAne (Set.Subset.antisymm (face_subset_toSet P hA) hsub)⟩
    have hhi0 := faceDim_lt_of_ssubset P hA (toSet_isFace P) hAss
    have hhi : Module.finrank ℝ (vectorSpan ℝ A) <
        Module.finrank ℝ (vectorSpan ℝ P.toSet) := hhi0
    omega
  obtain ⟨B, hB, hdB, heB, hBA⟩ :=
    seconda_faccetta P hfull e.property.1 e.property.2.1 hA hdA heA
  have hvA : v ∈ A := heA e.property.2.2
  have hvB : v ∈ B := heB e.property.2.2
  obtain ⟨eA, heAA, heAne, huniqA⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hA hdA hvA e heA
  obtain ⟨eB, heBB, heBne, huniqB⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hB hdB hvB e heB
  exact ⟨⟨A, B, hA, hdA, hB, hdB, heA, heB, hBA.symm,
    eA, eB, heAA, heBB, heAne, heBne⟩⟩

/-- Scelta canonica (classica) della stella di ogni spigolo. -/
noncomputable def stellaSpigolo (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) (e : SpigoloPer P v) :
    StellaSpigolo P v e :=
  Classical.choice (stella_spigolo_esiste P hfull hv e)

/-- Principio locale-globale sulla sezione, ricavato dal cono al taglio. -/
theorem locale_globale_taglio (P : ConvexPolytope 3) {v : E 3}
    (hv : v ∈ P.vertices) (l : E 3 →L[ℝ] ℝ) (c : ℝ) (hc : c < l v)
    (hvert : ∀ u ∈ P.vertices, u ≠ v → l u < c)
    (e : SpigoloPer P v) (D : StellaSpigolo P v e)
    (h : E 3 →L[ℝ] ℝ)
    (hA : h (SpigoloPer.taglio P v hv l c D.eA) ≤
      h (SpigoloPer.taglio P v hv l c e))
    (hB : h (SpigoloPer.taglio P v hv l c D.eB) ≤
      h (SpigoloPer.taglio P v hv l c e)) :
    ∀ z ∈ P.toSet ∩ {q | l q = c},
      h z ≤ h (SpigoloPer.taglio P v hv l c e) := by
  intro z hz
  obtain ⟨s, t, hs, ht, hzform⟩ :=
    cono_al_taglio P hv l c hc hvert e D.eA D.eB
      D.hA D.hdA (D.heA e.property.2.2)
      D.hB D.hdB (D.heB e.property.2.2)
      D.heA D.heB D.hAB D.heAA D.heBB D.heAne D.heBne z hz
  have hval : h z = h (SpigoloPer.taglio P v hv l c e) +
      s * (h (SpigoloPer.taglio P v hv l c D.eA) -
        h (SpigoloPer.taglio P v hv l c e)) +
      t * (h (SpigoloPer.taglio P v hv l c D.eB) -
        h (SpigoloPer.taglio P v hv l c e)) := by
    rw [hzform]
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
  rw [hval]
  nlinarith [mul_nonneg hs (by linarith : 0 ≤
      h (SpigoloPer.taglio P v hv l c e) -
        h (SpigoloPer.taglio P v hv l c D.eA)),
    mul_nonneg ht (by linarith : 0 ≤
      h (SpigoloPer.taglio P v hv l c e) -
        h (SpigoloPer.taglio P v hv l c D.eB))]

/-- Adiacenza fra spigoli del fan: sono contenuti in una stessa faccetta. -/
def CondividonoFaccetta (P : ConvexPolytope 3) (v : E 3)
    (e d : SpigoloPer P v) : Prop :=
  ∃ A : Set (E 3), P.IsFace A ∧ faceDim A = 2 ∧ e.val ⊆ A ∧ d.val ⊆ A

/-- La camminata del simplesso sulla sezione connette qualunque coppia di
spigoli per il vertice. -/
theorem spigoli_del_ventaglio_connessi (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) {v : E 3} (hv : v ∈ P.vertices)
    (e₀ es : SpigoloPer P v) :
    Relation.ReflTransGen (CondividonoFaccetta P v) e₀ es := by
  classical
  obtain ⟨l, c, hc, hvert⟩ := esiste_livello_separatore P hfull hv
  let Ds : StellaSpigolo P v es := stellaSpigolo P hfull hv es
  obtain ⟨lA, hmemA, hcharA⟩ := espositore_di_faccia P Ds.hA
  obtain ⟨lB, hmemB, hcharB⟩ := espositore_di_faccia P Ds.hB
  let h : E 3 →L[ℝ] ℝ := lA + lB
  let φ : SpigoloPer P v → ℝ :=
    fun e => h (SpigoloPer.taglio P v hv l c e)
  let FaceType := {f : Set (E 3) // P.IsFace f}
  letI : Fintype FaceType := (facce_finite P).fintype
  let incl : SpigoloPer P v → FaceType := fun e => ⟨e.val, e.property.1⟩
  have hincl : Function.Injective incl := by
    intro e d hed
    apply Subtype.ext
    exact congrArg (fun f : FaceType => f.val) hed
  letI : Fintype (SpigoloPer P v) := Fintype.ofInjective incl hincl
  let X : Finset (SpigoloPer P v) := Finset.univ
  have hlg : ∀ e ∈ X,
      (∀ d ∈ X, CondividonoFaccetta P v e d → φ d ≤ φ e) →
      ∀ z ∈ X, φ z ≤ φ e := by
    intro e heX hloc z hzX
    let D : StellaSpigolo P v e := stellaSpigolo P hfull hv e
    have hadjA : CondividonoFaccetta P v e D.eA :=
      ⟨D.A, D.hA, D.hdA, D.heA, D.heAA⟩
    have hadjB : CondividonoFaccetta P v e D.eB :=
      ⟨D.B, D.hB, D.hdB, D.heB, D.heBB⟩
    have hleA : h (SpigoloPer.taglio P v hv l c D.eA) ≤
        h (SpigoloPer.taglio P v hv l c e) := by
      exact hloc D.eA (by simp [X]) hadjA
    have hleB : h (SpigoloPer.taglio P v hv l c D.eB) ≤
        h (SpigoloPer.taglio P v hv l c e) := by
      exact hloc D.eB (by simp [X]) hadjB
    have haz : l (SpigoloPer.altro P v hv z) < c :=
      hvert _ (SpigoloPer.altro_spec P v hv z).1
        (SpigoloPer.altro_spec P v hv z).2.2.1
    have hxzK : SpigoloPer.taglio P v hv l c z ∈
        P.toSet ∩ {q | l q = c} := by
      refine ⟨face_subset_toSet P z.property.1
          (SpigoloPer.taglio_fatti P v hv l c hc z haz).1, ?_⟩
      exact (SpigoloPer.taglio_fatti P v hv l c hc z haz).2.1
    have hle := locale_globale_taglio P hv l c hc hvert e D h hleA hleB
      (SpigoloPer.taglio P v hv l c z) hxzK
    exact hle
  let xs : E 3 := SpigoloPer.taglio P v hv l c es
  have haes : l (SpigoloPer.altro P v hv es) < c :=
    hvert _ (SpigoloPer.altro_spec P v hv es).1
      (SpigoloPer.altro_spec P v hv es).2.2.1
  have hxse : xs ∈ es.val :=
    (SpigoloPer.taglio_fatti P v hv l c hc es haes).1
  have hxsA : xs ∈ Ds.A := Ds.heA hxse
  have hxsB : xs ∈ Ds.B := Ds.heB hxse
  have hmaxA : ∀ q ∈ P.toSet, lA q ≤ lA xs := (hmemA xs hxsA).2
  have hmaxB : ∀ q ∈ P.toSet, lB q ≤ lB xs := (hmemB xs hxsB).2
  have hinter : Ds.A ∩ Ds.B = es.val :=
    intersezione_faccette_eq_spigolo P es.property.1 es.property.2.1
      Ds.hA Ds.hdA Ds.hB Ds.hdB Ds.heA Ds.heB Ds.hAB
  have hunico : ∀ z ∈ X, z ≠ es → φ z < φ es := by
    intro z hzX hzes
    have haz : l (SpigoloPer.altro P v hv z) < c :=
      hvert _ (SpigoloPer.altro_spec P v hv z).1
        (SpigoloPer.altro_spec P v hv z).2.2.1
    let xz : E 3 := SpigoloPer.taglio P v hv l c z
    have hxze : xz ∈ z.val := (SpigoloPer.taglio_fatti P v hv l c hc z haz).1
    have hxzT : xz ∈ P.toSet := face_subset_toSet P z.property.1 hxze
    have hxzval : l xz = c :=
      (SpigoloPer.taglio_fatti P v hv l c hc z haz).2.1
    have hAle : lA xz ≤ lA xs := hmaxA xz hxzT
    have hBle : lB xz ≤ lB xs := hmaxB xz hxzT
    have hsumle : φ z ≤ φ es := by
      dsimp [φ, h]
      simp only [add_apply]
      change lA xz + lB xz ≤ lA xs + lB xs
      linarith
    rcases lt_or_eq_of_le hsumle with hlt | heq
    · exact hlt
    · exfalso
      have heqsum : lA xz + lB xz = lA xs + lB xs := by
        simpa [φ, h, xz, xs] using heq
      have heqA : lA xz = lA xs := by linarith
      have heqB : lB xz = lB xs := by linarith
      have hxzA : xz ∈ Ds.A := hcharA xz hxzT
        (fun q hq => le_trans (hmaxA q hq) (le_of_eq heqA.symm))
      have hxzB : xz ∈ Ds.B := hcharB xz hxzT
        (fun q hq => le_trans (hmaxB q hq) (le_of_eq heqB.symm))
      have hxzes : xz ∈ es.val := by
        rw [← hinter]
        exact ⟨hxzA, hxzB⟩
      have hxsing : xz ∈ ({xs} : Set (E 3)) := by
        rw [← (SpigoloPer.taglio_fatti P v hv l c hc es haes).2.2]
        exact ⟨hxzes, hxzval⟩
      have hxzeq : xz = xs := Set.mem_singleton_iff.mp hxsing
      have hdist := tagli_distinti P hv l c hc z es hzes haz haes
      exact hdist hxzeq
  have hwalk := camminata_del_simplesso X (CondividonoFaccetta P v) φ
    hlg (xs := es) (by simp [X]) hunico (x₀ := e₀) (by simp [X])
  exact Relation.ReflTransGen.mono (fun _ _ hstep => hstep.2) _ _ hwalk

/-- Ogni faccetta che contiene `v` contiene uno spigolo per `v`. -/
theorem esiste_spigolo_nella_faccetta (P : ConvexPolytope 3)
    {v : E 3} (hv : v ∈ P.vertices)
    {A : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A) :
    ∃ e : SpigoloPer P v, e.val ⊆ A := by
  classical
  let Q : ConvexPolytope 3 := facePolytope P hA
  have hQT : Q.toSet = A := facePolytope_toSet P hA
  have hQdim : Module.finrank ℝ (vectorSpan ℝ Q.toSet) = 2 := by
    rw [hQT]
    exact hdA
  have hvQ : v ∈ Q.vertices := Finset.mem_filter.mpr ⟨hv, hvA⟩
  have hvface : Q.IsFace ({v} : Set (E 3)) := vertex_isFace Q hvQ
  have hgap : faceDim ({v} : Set (E 3)) + 2 ≤
      Module.finrank ℝ (vectorSpan ℝ Q.toSet) := by
    rw [faceDim_singleton, hQdim]
  obtain ⟨g, hgQ, hvg, hgne⟩ := interpolazione Q hvface hgap
  have hdg : faceDim g = 1 := by
    show Module.finrank ℝ (vectorSpan ℝ g) = 1
    have hlo0 := faceDim_lt_of_ssubset Q hvface hgQ hvg
    have hlo : Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E 3))) <
        Module.finrank ℝ (vectorSpan ℝ g) := hlo0
    have hdv : Module.finrank ℝ (vectorSpan ℝ ({v} : Set (E 3))) = 0 :=
      faceDim_singleton v
    have hgss : g ⊂ Q.toSet :=
      ⟨face_subset_toSet Q hgQ, fun hsub =>
        hgne (Set.Subset.antisymm (face_subset_toSet Q hgQ) hsub)⟩
    have hhi0 := faceDim_lt_of_ssubset Q hgQ (toSet_isFace Q) hgss
    have hhi : Module.finrank ℝ (vectorSpan ℝ g) <
        Module.finrank ℝ (vectorSpan ℝ Q.toSet) := hhi0
    omega
  have hgP : P.IsFace g := isFace_of_facePolytope P hA hgQ
  have hgA : g ⊆ A := by
    have := face_subset_toSet Q hgQ
    rwa [hQT] at this
  have hvgmem : v ∈ g := hvg.subset (Set.mem_singleton v)
  exact ⟨⟨g, hgP, hdg, hvgmem⟩, hgA⟩

/-- Trasferimento di un cammino di spigoli a un cammino di faccette. -/
theorem trasferisci_cammino_spigoli (P : ConvexPolytope 3) {v : E 3}
    {A : Set (E 3)} (_hA : P.IsFace A) (_hdA : faceDim A = 2) (_hvA : v ∈ A)
    {e₀ es : SpigoloPer P v} (he₀A : e₀.val ⊆ A)
    (hcam : Relation.ReflTransGen (CondividonoFaccetta P v) e₀ es) :
    ∀ {B : Set (E 3)}, P.IsFace B → faceDim B = 2 → v ∈ B → es.val ⊆ B →
      Relation.ReflTransGen
        (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧
          SpigoloComune P v X Y) A B := by
  induction hcam with
  | refl =>
      intro B hB hdB hvB heB
      apply Relation.ReflTransGen.single
      exact ⟨⟨hB, hdB, hvB⟩,
        ⟨e₀.val, e₀.property.1, e₀.property.2.1, e₀.property.2.2,
          he₀A, heB⟩⟩
  | @tail b d hprev hadj ih =>
      intro B hB hdB hvB hdBsub
      obtain ⟨C, hC, hdC, hbC, hdCsub⟩ := hadj
      have hvC : v ∈ C := hbC b.property.2.2
      have hAC := ih hC hdC hvC hbC
      have hCB : Relation.ReflTransGen
          (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧
            SpigoloComune P v X Y) C B := by
        apply Relation.ReflTransGen.single
        exact ⟨⟨hB, hdB, hvB⟩,
          ⟨d.val, d.property.1, d.property.2.1, d.property.2.2,
            hdCsub, hdBsub⟩⟩
      exact hAC.trans hCB

theorem ventaglio_connesso (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices)
    {A B : Set (E 3)} (hA : P.IsFace A) (hdA : faceDim A = 2) (hvA : v ∈ A)
    (hB : P.IsFace B) (hdB : faceDim B = 2) (hvB : v ∈ B) :
    Relation.ReflTransGen
      (fun X Y => (P.IsFace Y ∧ faceDim Y = 2 ∧ v ∈ Y) ∧ SpigoloComune P v X Y)
      A B := by
  obtain ⟨eA, heAA⟩ := esiste_spigolo_nella_faccetta P hv hA hdA hvA
  obtain ⟨eB, heBB⟩ := esiste_spigolo_nella_faccetta P hv hB hdB hvB
  have hcam := spigoli_del_ventaglio_connessi P hfull hv eA eB
  exact trasferisci_cammino_spigoli P hA hdA hvA heAA hcam hB hdB hvB heBB

/-- In un politopo full-dimensional di `ℝ³`, ogni vertice appartiene ad
almeno tre faccette a due a due distinte. -/
theorem tre_faccette_al_vertice_conn (P : ConvexPolytope 3) (hfull : P.IsFullDim)
    {v : E 3} (hv : v ∈ P.vertices) :
    ∃ A B C : Set (E 3),
      P.IsFace A ∧ faceDim A = 2 ∧ v ∈ A ∧
      P.IsFace B ∧ faceDim B = 2 ∧ v ∈ B ∧
      P.IsFace C ∧ faceDim C = 2 ∧ v ∈ C ∧
      A ≠ B ∧ A ≠ C ∧ B ≠ C := by
  classical
  obtain ⟨F, hFv⟩ := bandiera_al_vertice P hfull hv
  have hve : v ∈ F.face 1 := by
    have hsub := (F.strict_mono 0 1 (by decide)).subset
    apply hsub
    rw [hFv]
    exact Set.mem_singleton v
  let e : SpigoloPer P v :=
    ⟨F.face 1, F.isFace 1, F.dim_eq 1, hve⟩
  let A : Set (E 3) := F.face 2
  have hA : P.IsFace A := F.isFace 2
  have hdA : faceDim A = 2 := F.dim_eq 2
  have heA : e.val ⊆ A := (F.strict_mono 1 2 (by decide)).subset
  have hvA : v ∈ A := heA e.property.2.2
  obtain ⟨B, hB, hdB, heB, hBA⟩ :=
    seconda_faccetta P hfull e.property.1 e.property.2.1 hA hdA heA
  have hvB : v ∈ B := heB e.property.2.2
  obtain ⟨e', he'A, he'ne, huniq⟩ :=
    unico_altro_spigolo_nella_faccetta P hv hA hdA hvA e heA
  obtain ⟨C, hC, hdC, he'C, hCA⟩ :=
    seconda_faccetta P hfull e'.property.1 e'.property.2.1 hA hdA he'A
  have hvC : v ∈ C := he'C e'.property.2.2
  have hAB : A ≠ B := hBA.symm
  have hAC : A ≠ C := hCA.symm
  have hBC : B ≠ C := by
    intro hBCeq
    have hinter : A ∩ B = e.val :=
      intersezione_faccette_eq_spigolo P e.property.1 e.property.2.1
        hA hdA hB hdB heA heB hAB
    let p : E 3 := SpigoloPer.altro P v hv e'
    have hpe' : p ∈ e'.val := (SpigoloPer.altro_spec P v hv e').2.1
    have hpv : p ≠ v := (SpigoloPer.altro_spec P v hv e').2.2.1
    have hpB : p ∈ B := by
      rw [hBCeq]
      exact he'C hpe'
    have hpe : p ∈ e.val := by
      rw [← hinter]
      exact ⟨he'A hpe', hpB⟩
    have heq := spigoli_eq_of_punto_comune P e'.property.1 e'.property.2.1
      e'.property.2.2 e.property.1 e.property.2.1 e.property.2.2
      hpe' hpe hpv
    exact he'ne (Subtype.ext heq)
  exact ⟨A, B, C, hA, hdA, hvA, hB, hdB, hvB, hC, hdC, hvC,
    hAB, hAC, hBC⟩

end LeanEval.Geometry.PlatonicClassification

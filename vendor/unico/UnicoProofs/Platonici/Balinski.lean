/- Modified for the ClassicalTheorems project by Codex on 2026-10-02:
   compatibility updates for Lean 4.34.0 and the pinned mathlib revision. -/

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.ConnessioneVentaglio
import UnicoProofs.Platonici.BandieraVertice
import UnicoProofs.Platonici.VerticiFaccette
import UnicoProofs.Platonici.FacceConnesse

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

instance spigoloPer_finito (P : ConvexPolytope 3) (v : E 3) :
    Finite (SpigoloPer P v) := by
  let FaceType := {f : Set (E 3) // P.IsFace f}
  letI : Fintype FaceType := (facce_finite P).fintype
  let incl : SpigoloPer P v → FaceType := fun e => ⟨e.val, e.property.1⟩
  have hincl : Function.Injective incl := by
    intro e d hed
    apply Subtype.ext
    exact congrArg (fun f : FaceType => f.val) hed
  exact Finite.of_injective incl hincl

theorem locale_globale_vertice (P : ConvexPolytope 3)
    (hfull : P.IsFullDim) {v : E 3} (hv : v ∈ P.vertices)
    (h : E 3 →L[ℝ] ℝ)
    (hloc : ∀ e : SpigoloPer P v, h (SpigoloPer.altro P v hv e) ≤ h v) :
    ∀ z ∈ P.toSet, h z ≤ h v := by
  classical
  obtain ⟨l, c, hc, hvert⟩ := esiste_livello_separatore P hfull hv
  obtain ⟨F, hFv⟩ := bandiera_al_vertice P hfull hv
  have hvone : v ∈ F.face 1 := by
    have hsub := (F.strict_mono 0 1 (by decide)).subset
    apply hsub
    rw [hFv]
    exact Set.mem_singleton v
  let e0 : SpigoloPer P v :=
    ⟨F.face 1, F.isFace 1, F.dim_eq 1, hvone⟩
  letI : Fintype (SpigoloPer P v) := Fintype.ofFinite _
  let X : Finset (SpigoloPer P v) := Finset.univ
  let phi : SpigoloPer P v → ℝ :=
    fun e => h (SpigoloPer.taglio P v hv l c e)
  have hXne : X.Nonempty := ⟨e0, Finset.mem_univ e0⟩
  obtain ⟨emax, hemaxX, hemax⟩ := X.exists_max_image phi hXne
  let D : StellaSpigolo P v emax := stellaSpigolo P hfull hv emax
  have hmaxA :
      h (SpigoloPer.taglio P v hv l c D.eA) ≤
        h (SpigoloPer.taglio P v hv l c emax) := by
    exact hemax D.eA (Finset.mem_univ D.eA)
  have hmaxB :
      h (SpigoloPer.taglio P v hv l c D.eB) ≤
        h (SpigoloPer.taglio P v hv l c emax) := by
    exact hemax D.eB (Finset.mem_univ D.eB)
  have hsection : ∀ y ∈ P.toSet ∩ {q | l q = c},
      h y ≤ h (SpigoloPer.taglio P v hv l c emax) :=
    locale_globale_taglio P hv l c hc hvert emax D h hmaxA hmaxB
  have hcut_le : ∀ e : SpigoloPer P v,
      h (SpigoloPer.taglio P v hv l c e) ≤ h v := by
    intro e
    let a : E 3 := SpigoloPer.altro P v hv e
    let t : ℝ := (l v - c) / (l v - l a)
    have haV : a ∈ P.vertices := (SpigoloPer.altro_spec P v hv e).1
    have hane : a ≠ v := (SpigoloPer.altro_spec P v hv e).2.2.1
    have hal : l a < c := hvert a haV hane
    have hden : 0 < l v - l a := by linarith
    have hnum : 0 < l v - c := by linarith
    have ht : 0 < t := div_pos hnum hden
    have hform :
        h (SpigoloPer.taglio P v hv l c e) =
          h v + t * (h a - h v) := by
      simp only [SpigoloPer.taglio, a, t, map_add, map_smul, map_sub,
        smul_eq_mul]
    rw [hform]
    have hha : h a - h v ≤ 0 := sub_nonpos.mpr (hloc e)
    have hmul : t * (h a - h v) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hha
    linarith
  have hver_le : ∀ u ∈ P.vertices, h u ≤ h v := by
    intro u hu
    by_cases huv : u = v
    · subst u
      exact le_rfl
    · have hul : l u < c := hvert u hu huv
      let t : ℝ := (l v - c) / (l v - l u)
      let y : E 3 := v + t • (u - v)
      have hden : 0 < l v - l u := by linarith
      have hnum : 0 < l v - c := by linarith
      have ht : 0 < t := div_pos hnum hden
      have htone : t < 1 := by
        rw [div_lt_one hden]
        linarith
      have hyform : y = (1 - t) • v + t • u := by
        dsimp [y]
        module
      have hyseg : y ∈ segment ℝ v u := by
        refine ⟨1 - t, t, by linarith, ht.le, by ring, hyform.symm⟩
      have hvT : v ∈ P.toSet := subset_convexHull ℝ _ hv
      have huT : u ∈ P.toSet := subset_convexHull ℝ _ hu
      have hyT : y ∈ P.toSet :=
        (convex_convexHull ℝ (P.vertices : Set (E 3))).segment_subset hvT huT hyseg
      have hylevel : l y = c := by
        dsimp [y, t]
        simp only [map_add, map_smul, map_sub, smul_eq_mul]
        have hdenne : l v - l u ≠ 0 := ne_of_gt hden
        have hcancel :
            (l v - c) / (l v - l u) * (l v - l u) = l v - c :=
          div_mul_cancel₀ _ hdenne
        nlinarith
      have hyle : h y ≤ h v :=
        le_trans (hsection y ⟨hyT, hylevel⟩) (hcut_le emax)
      have hyh : h y = h v + t * (h u - h v) := by
        dsimp [y]
        simp only [map_add, map_smul, map_sub, smul_eq_mul]
      rw [hyh] at hyle
      by_contra hnot
      have hpos : 0 < h u - h v := sub_pos.mpr (lt_of_not_ge hnot)
      have := mul_pos ht hpos
      linarith
  intro z hz
  have hsub : P.toSet ⊆ {q : E 3 | h q ≤ h v} := by
    show convexHull ℝ (P.vertices : Set (E 3)) ⊆ {q : E 3 | h q ≤ h v}
    apply convexHull_min
    · intro u hu
      exact hver_le u hu
    · exact convex_halfSpace_le (LinearMap.isLinear h.toLinearMap) (h v)
  exact hsub hz

theorem balinski_light (P : ConvexPolytope 3) (hfull : P.IsFullDim) :
    ∀ u ∈ P.vertices, ∀ w ∈ P.vertices,
      Relation.ReflTransGen (AdiacentiVertici P) u w := by
  classical
  intro u hu w hw
  obtain ⟨l, c, hc, hvert⟩ := esiste_livello_separatore P hfull hw
  let X : Finset (E 3) := P.vertices
  have hlg : ∀ x ∈ X,
      (∀ y ∈ X, AdiacentiVertici P x y → l y ≤ l x) →
      ∀ z ∈ X, l z ≤ l x := by
    intro x hx hlocal z hz
    have hedge : ∀ e : SpigoloPer P x,
        l (SpigoloPer.altro P x hx e) ≤ l x := by
      intro e
      have ha := SpigoloPer.altro_spec P x hx e
      apply hlocal (SpigoloPer.altro P x hx e) ha.1
      exact ⟨hx, ha.1, e.val, e.property.1, e.property.2.1,
        e.property.2.2, ha.2.1, ha.2.2.1.symm⟩
    exact locale_globale_vertice P hfull hx l hedge z
      (subset_convexHull ℝ _ hz)
  have hunico : ∀ z ∈ X, z ≠ w → l z < l w := by
    intro z hz hzw
    have := hvert z hz hzw
    linarith
  have hwalk := camminata_del_simplesso X (AdiacentiVertici P) l
    hlg hw hunico hu
  exact Relation.ReflTransGen.mono (fun _ _ hstep => hstep.2) _ _ hwalk

end LeanEval.Geometry.PlatonicClassification

import Mathlib
import UnicoProofs.Platonici.Benchmark
import UnicoProofs.Platonici.PerturbazioneFinita
import UnicoProofs.Platonici.SottoPolitopo

/-!
FASE 3A, Q3-S3b — FACCIA STRETTA ⟹ DIMENSIONE STRETTA (18 lug 2026).

Se f ⊊ g sono facce di un politopo, dim f < dim g. Via il sotto-politopo:
f è faccia propria di g; il suo espositore l non è costante su g (il vertice
fuori sta sotto il massimo); se le dimensioni fossero pari, gli span affini
coinciderebbero e l sarebbe costante su aff(g): assurdo.
-/

open Set Metric
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

open Classical in
/-- S3b: tra facce, l'inclusione stretta forza la dimensione stretta. -/
theorem faceDim_lt_of_ssubset (P : ConvexPolytope n) {f g : Set (E n)}
    (hf : P.IsFace f) (hg : P.IsFace g) (hsub : f ⊂ g) :
    faceDim f < faceDim g := by
  classical
  -- f è faccia del sotto-politopo di g
  have hfQ : (facePolytope P hg).IsFace f :=
    facePolytope_isFace_of P hg hf hsub.1
  -- un vertice di g fuori da f
  have hgconv : Convex ℝ g := hg.1.convex (convex_convexHull ℝ _)
  have hout : ∃ w ∈ (facePolytope P hg).vertices, w ∉ f := by
    by_contra hall
    push_neg at hall
    have hsubg : g ⊆ f := by
      have h1 : g = (facePolytope P hg).toSet := (facePolytope_toSet P hg).symm
      rw [h1]
      have hsubv : ((facePolytope P hg).vertices : Set (E n)) ⊆ f := fun w hw =>
        hall w (by exact_mod_cast hw)
      have hfconv : Convex ℝ f := hf.1.convex (convex_convexHull ℝ _)
      exact convexHull_min hsubv hfconv
    exact hsub.2 hsubg
  obtain ⟨w, hwV, hwf⟩ := hout
  have hwg : w ∈ g := by
    have h1 : w ∈ (facePolytope P hg).toSet :=
      subset_convexHull ℝ _ (by exact_mod_cast hwV)
    rwa [facePolytope_toSet P hg] at h1
  -- l'espositore di f dentro g
  obtain ⟨l, hl⟩ := hfQ.1 hf.2
  rw [facePolytope_toSet P hg] at hl
  obtain ⟨x₀, hx₀⟩ := hf.2
  have hx₀' := hx₀
  rw [hl] at hx₀'
  set M : ℝ := l x₀ with hM
  have hlf : ∀ z ∈ f, l z = M := by
    intro z hz
    have hz' := hz
    rw [hl] at hz'
    exact le_antisymm (hx₀'.2 z hz'.1) (hz'.2 x₀ hx₀'.1)
  have hlw : l w < M := by
    rcases lt_or_eq_of_le (hx₀'.2 w hwg) with h | h
    · exact h
    · exfalso
      apply hwf
      rw [hl]
      exact ⟨hwg, fun y hy => h ▸ hx₀'.2 y hy⟩
  -- dimensioni: ≤ dalla monotonia; se pari, span affini uguali
  have hmono : vectorSpan ℝ f ≤ vectorSpan ℝ g :=
    vectorSpan_mono ℝ hsub.1
  have hle : faceDim f ≤ faceDim g := Submodule.finrank_mono hmono
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hspan_eq : vectorSpan ℝ f = vectorSpan ℝ g := by
      apply Submodule.eq_of_le_of_finrank_le hmono
      show faceDim g ≤ faceDim f
      exact le_of_eq heq.symm
    have haff_le : affineSpan ℝ f ≤ affineSpan ℝ g := affineSpan_mono ℝ hsub.1
    have haff_eq : affineSpan ℝ f = affineSpan ℝ g := by
      have hx₀m : x₀ ∈ affineSpan ℝ f := subset_affineSpan ℝ _ hx₀
      apply le_antisymm haff_le
      intro y hy
      have hdir : (affineSpan ℝ f).direction = (affineSpan ℝ g).direction := by
        rw [direction_affineSpan, direction_affineSpan, hspan_eq]
      have h1 : y -ᵥ x₀ ∈ (affineSpan ℝ g).direction :=
        AffineSubspace.vsub_mem_direction hy (haff_le hx₀m)
      rw [← hdir] at h1
      have := AffineSubspace.vadd_mem_of_mem_direction h1 hx₀m
      simpa using this
    -- l è costante su affineSpan f = affineSpan g ∋ w: assurdo
    have hconst : ∀ y ∈ affineSpan ℝ f, l y = M := by
      intro y hy
      have heqon : Set.EqOn (⇑l.toLinearMap.toAffineMap)
          (⇑(AffineMap.const ℝ (E n) M)) f := by
        intro z hz
        simp [hlf z hz]
      have h2 := AffineMap.eqOn_affineSpan (k := ℝ) heqon  -- nome da verificare
      have := h2 hy
      simpa using this
    have hw_aff : w ∈ affineSpan ℝ f := by
      rw [haff_eq]
      exact subset_affineSpan ℝ _ hwg
    have := hconst w hw_aff
    linarith

end LeanEval.Geometry.PlatonicClassification

import Mathlib
import UnicoProofs.Platonici.Benchmark

/-!
FASE 3A, Q3-S3a — DUE FUNZIONALI INDIPENDENTI DALLA CODIMENSIONE ≥ 2.

Il pezzo di algebra lineare dell'interpolazione: se U ≤ W con
finrank U + 2 ≤ finrank W, il complemento ortogonale di U dentro W contiene
due vettori linearmente indipendenti (i cui funzionali interni si annullano
su U). Serviranno per i due perni del trucco di S3.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

variable {n : ℕ}

/-- Dalla codimensione ≥ 2: due vettori indipendenti in W ⊓ Uᗮ. -/
theorem exists_two_orthogonal_indep {U W : Submodule ℝ (E n)}
    (hUW : U ≤ W) (hcodim : Module.finrank ℝ U + 2 ≤ Module.finrank ℝ W) :
    ∃ w₁ w₂ : E n, w₁ ∈ W ∧ w₂ ∈ W ∧
      (∀ u ∈ U, ⟪w₁, u⟫ = 0) ∧ (∀ u ∈ U, ⟪w₂, u⟫ = 0) ∧
      LinearIndependent ℝ ![w₁, w₂] := by
  classical
  -- il complemento ortogonale relativo V := Uᗮ ⊓ W ha finrank ≥ 2
  set V : Submodule ℝ (E n) := Uᗮ ⊓ W with hV
  have hdim : Module.finrank ℝ U + Module.finrank ℝ V = Module.finrank ℝ W := by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal hUW
    rw [hV]
    rw [inf_comm] at h1 ⊢
    exact h1
  have hVdim : 2 ≤ Module.finrank ℝ V := by omega
  -- due vettori indipendenti in V
  obtain ⟨v, hvV, hv0⟩ : ∃ v ∈ V, v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : V = ⊥ := by
      ext x
      simp only [Submodule.mem_bot]
      exact ⟨fun hx => hall x hx, fun hx => hx ▸ V.zero_mem⟩
    rw [this] at hVdim
    simp at hVdim
  -- lo span di v dentro V non è tutto V (finrank 1 < 2): esiste v' fuori
  have hspan_lt : Module.finrank ℝ (Submodule.span ℝ {v}) < Module.finrank ℝ V := by
    rw [finrank_span_singleton hv0]
    omega
  obtain ⟨v', hv'V, hv'span⟩ : ∃ v' ∈ V, v' ∉ Submodule.span ℝ {v} := by
    by_contra hall
    push_neg at hall
    have hle : V ≤ Submodule.span ℝ {v} := fun x hx => hall x hx
    have := Submodule.finrank_mono hle
    omega
  refine ⟨v, v', hvV.2, hv'V.2, ?_, ?_, ?_⟩
  · intro u hu
    have h1 : v ∈ Uᗮ := hvV.1
    have h2 := (Submodule.mem_orthogonal U v).mp h1 u hu
    rw [real_inner_comm]
    exact h2
  · intro u hu
    have h1 : v' ∈ Uᗮ := hv'V.1
    have h2 := (Submodule.mem_orthogonal U v').mp h1 u hu
    rw [real_inner_comm]
    exact h2
  · rw [linearIndependent_fin2]
    constructor
    · intro h
      have h' : v' = 0 := h
      apply hv'span
      rw [h']
      exact Submodule.zero_mem _
    · intro a h
      have h' : v = a • v' := h.symm
      by_cases ha : a = 0
      · subst ha
        simp at h'
        exact hv0 h'
      · apply hv'span
        have hvv : v' = a⁻¹ • v := by
          rw [h', smul_smul, inv_mul_cancel₀ ha, one_smul]
        rw [hvv]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

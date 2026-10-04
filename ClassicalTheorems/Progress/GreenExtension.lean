/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.MeanValue

/-! Compactly supported C¹ extensions for the neighborhood fields in Green’s theorem. -/
noncomputable section
open Set Function
open scoped NNReal
namespace ClassicalTheorems.Progress.Green

/-- A C¹ map near a compact set in a finite-dimensional real space admits a
compactly supported global C¹ extension agreeing on an open neighborhood. -/
theorem exists_compactSupport_extension_vector
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K U : Set E) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (P : E → F) (hP : ContDiffOn ℝ 1 P U) :
    ∃ (R : E → F) (W : Set E), ContDiff ℝ 1 R ∧ HasCompactSupport R ∧
      IsOpen W ∧ K ⊆ W ∧ EqOn R P W := by
  obtain ⟨V, hVopen, hKV, hVU, hVcpt⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWopen, hKW, hWV, _⟩ :=
    exists_open_between_and_isCompact_closure hK hVopen hKV
  obtain ⟨f, hf, _, hsupport, hone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := 1) hVopen isClosed_closure hWV
  let R : E → F := fun z => f z • P z
  have hR : ContDiff ℝ 1 R := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hf.contDiffAt.smul (hP.contDiffAt (hU.mem_nhds hz))
    · have hzV : z ∉ closure V := fun h => hz (hVU h)
      have heq : R =ᶠ[nhds z] (fun _ => (0 : F)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzV] with w hw
        have hwf : w ∉ support f := by
          rw [hsupport]
          exact fun h => hw (subset_closure h)
        have hw0 : f w = 0 := notMem_support.mp hwf
        simp [R, hw0]
      exact (contDiff_const.contDiffAt : ContDiffAt ℝ 1 (fun _ : E => (0 : F)) z).congr_of_eventuallyEq heq
  have hfcpt : HasCompactSupport f := by
    change IsCompact (closure (support f))
    rwa [hsupport]
  refine ⟨R, W, hR, hfcpt.smul_right, hWopen, hKW, ?_⟩
  intro z hz
  have hf1 : f z = 1 := (hone z).mp (subset_closure hz)
  simp [R, hf1]


/-- A C¹ scalar field near a compact complex set admits a compactly supported
global C¹ extension agreeing on an open neighborhood of that set. -/
theorem exists_compactSupport_extension (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (P : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) :
    ∃ (R : ℂ → ℝ) (W : Set ℂ), ContDiff ℝ 1 R ∧ HasCompactSupport R ∧
      IsOpen W ∧ K ⊆ W ∧ EqOn R P W :=
  exists_compactSupport_extension_vector K U hK hU hKU P hP

/-- A compactly supported C¹ field has a uniform derivative bound and is globally Lipschitz. -/
theorem compactSupport_lipschitz (P : ℂ → ℝ) (hP : ContDiff ℝ 1 P)
    (hcpt : HasCompactSupport P) :
    ∃ K : ℝ≥0, LipschitzWith K P ∧ ∀ z, ‖fderiv ℝ P z‖ ≤ K := by
  obtain ⟨C, hC⟩ := (hP.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hcpt.fderiv (𝕜 := ℝ))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb (z : ℂ) : ‖fderiv ℝ P z‖ ≤ K := (hC z).trans (le_max_left _ _)
  refine ⟨K, lipschitzWith_of_nnnorm_fderiv_le (hP.differentiable one_ne_zero) ?_, hb⟩
  intro z
  exact_mod_cast hb z

/-- Agreement on an open neighborhood preserves the actual Frechet derivative. -/
theorem fderiv_eq_of_eqOn_open (P R : ℂ → ℝ) (W : Set ℂ) (hW : IsOpen W)
    (hEq : EqOn R P W) {z : ℂ} (hz : z ∈ W) : fderiv ℝ R z = fderiv ℝ P z := by
  apply Filter.EventuallyEq.fderiv_eq
  exact Filter.mem_of_superset (hW.mem_nhds hz) (fun w hw => hEq hw)

/-- The fields of Green’s theorem can be replaced near the compact domain by globally
Lipschitz, compactly supported C¹ fields, preserving values and derivatives. -/
theorem exists_lipschitz_extension (K U : Set ℂ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (P : ℂ → ℝ) (hP : ContDiffOn ℝ 1 P U) :
    ∃ (R : ℂ → ℝ) (W : Set ℂ) (L : ℝ≥0), ContDiff ℝ 1 R ∧ HasCompactSupport R ∧
      LipschitzWith L R ∧ (∀ z, ‖fderiv ℝ R z‖ ≤ L) ∧
      IsOpen W ∧ K ⊆ W ∧ EqOn R P W ∧ EqOn (fderiv ℝ R) (fderiv ℝ P) W := by
  obtain ⟨R, W, hR, hcpt, hW, hKW, hEq⟩ :=
    exists_compactSupport_extension K U hK hU hKU P hP
  obtain ⟨L, hLip, hBound⟩ := compactSupport_lipschitz R hR hcpt
  exact ⟨R, W, L, hR, hcpt, hLip, hBound, hW, hKW, hEq,
    fun _ hz => fderiv_eq_of_eqOn_open P R W hW hEq hz⟩

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.exists_compactSupport_extension

#check_upstream ClassicalTheorems.Progress.Green.compactSupport_lipschitz
#check_upstream ClassicalTheorems.Progress.Green.fderiv_eq_of_eqOn_open
#check_upstream ClassicalTheorems.Progress.Green.exists_lipschitz_extension

#check_upstream ClassicalTheorems.Progress.Green.exists_compactSupport_extension_vector

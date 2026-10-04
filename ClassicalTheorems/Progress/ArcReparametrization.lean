/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.MonotoneContinuity

/-! C¹ change of parameter from a positive continuous density. Adding ε to speed
allows this construction even when a C¹ curve has stationary points. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem surjective_of_deriv_ge_pos (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (q : ℝ) (hq : 0 < q) (hbound : ∀ t, q ≤ deriv f t) : Function.Surjective f := by
  intro y
  apply mem_range_of_exists_le_of_exists_ge hf.continuous
  · let a := min ((y - f 0) / q) 0
    have ha : a ≤ 0 := min_le_right _ _
    have hqa : q * a ≤ y - f 0 := by
      have h := mul_le_mul_of_nonneg_left (min_le_left ((y - f 0) / q) 0) hq.le
      dsimp only [a]
      calc
        _ ≤ q * ((y - f 0) / q) := h
        _ = y - f 0 := by field_simp
    have h := mul_sub_le_image_sub_of_le_deriv hf hbound ha
    exact ⟨a, by nlinarith⟩
  · let b := max ((y - f 0) / q) 0
    have hb : 0 ≤ b := le_max_right _ _
    have hqb : y - f 0 ≤ q * b := by
      have h := mul_le_mul_of_nonneg_left (le_max_left ((y - f 0) / q) 0) hq.le
      dsimp only [b]
      calc
        _ = q * ((y - f 0) / q) := by field_simp
        _ ≤ _ := h
    have h := mul_sub_le_image_sub_of_le_deriv hf hbound hb
    exact ⟨b, by nlinarith⟩

/-- An increasing C¹ parameter change fixing 0 and 1, whose speed cancels a
positive continuous density. The density need not itself be differentiable. -/
theorem positive_density_reparametrization (w : ℝ → ℝ) (hw : Continuous w)
    (ε : ℝ) (hε : 0 < ε) (hlower : ∀ t, ε ≤ w t) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ StrictMono φ ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      (∀ t, HasDerivAt φ ((∫ s in (0 : ℝ)..1, w s) / w (φ t)) t) := by
  let A := fun t => ∫ s in (0 : ℝ)..t, w s
  let L := ∫ s in (0 : ℝ)..1, w s
  have hd (t : ℝ) : HasDerivAt A (w t) t :=
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
      hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hA : ContDiff ℝ 1 A := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    convert hw using 1
    ext t
    exact (hd t).deriv
  have hwp (t : ℝ) : 0 < w t := lt_of_lt_of_le hε (hlower t)
  have hmono : StrictMono A := strictMono_of_deriv_pos (fun t => by rw [(hd t).deriv]; exact hwp t)
  have hsurj : Function.Surjective A := surjective_of_deriv_ge_pos A
    (fun t => (hd t).differentiableAt) ε hε (fun t => by rw [(hd t).deriv]; exact hlower t)
  let e : ℝ ≃ₜ ℝ := (hmono.orderIsoOfSurjective A hsurj).toHomeomorph
  have he (t : ℝ) : e t = A t := rfl
  have he0 : e 0 = 0 := by simp [he, A]
  have he1 : e 1 = L := rfl
  have hL : 0 < L := by
    have h := hmono (by norm_num : (0 : ℝ) < 1)
    change e 0 < e 1 at h
    rwa [he0, he1] at h
  have heC : ContDiff ℝ 1 (e.symm : ℝ → ℝ) :=
    e.contDiff_symm_deriv (fun t => (hwp t).ne') hd hA
  let φ : ℝ → ℝ := fun t => e.symm (L * t)
  have hφ : ContDiff ℝ 1 φ := heC.comp (contDiff_const.mul contDiff_id)
  have hφmono : StrictMono φ := by
    intro a b hab
    exact (hmono.orderIsoOfSurjective A hsurj).symm.strictMono
      (mul_lt_mul_of_pos_left hab hL)
  have hφ0 : φ 0 = 0 := by
    apply e.injective
    simp only [φ, mul_zero, e.apply_symm_apply, he0]
  have hφ1 : φ 1 = 1 := by
    apply e.injective
    simp only [φ, mul_one, e.apply_symm_apply, he1]
  refine ⟨φ, hφ, hφmono, hφ0, hφ1, ?_⟩
  intro t
  have hinv : HasDerivAt (e.symm : ℝ → ℝ) (w (e.symm (L * t)))⁻¹ (L * t) :=
    (hd (e.symm (L * t))).of_local_left_inverse e.symm.continuous.continuousAt
      (hwp _).ne' (Filter.Eventually.of_forall e.apply_symm_apply)
  convert hinv.comp t ((hasDerivAt_id t).const_mul L) using 1 <;>
    simp [φ, L, Function.comp_def, div_eq_mul_inv, mul_comm]

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.positive_density_reparametrization

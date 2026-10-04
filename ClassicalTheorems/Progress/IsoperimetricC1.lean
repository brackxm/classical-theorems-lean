/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricEquality
import ClassicalTheorems.Progress.ArcReparametrization
import Mathlib.Topology.Order.OrderClosed

/-! The sharp perimeter bound for arbitrary C¹ closed curves. Positive-density
reparametrization and an ε limit remove the constant-speed assumption, including
at stationary points. Geometric Jordan area is then supplied by Green. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ClassicalTheorems.Progress.Isoperimetric

theorem deriv_reparam (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (t : ℝ) :
    deriv (γ ∘ φ) t = deriv φ t • deriv γ (φ t) :=
  ((hγ.differentiable one_ne_zero (φ t)).hasDerivAt.scomp t
    (hφ.differentiable one_ne_zero t).hasDerivAt).deriv

theorem reparam_signed_area (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1) :
    (∫ t in (0 : ℝ)..1, (γ (φ t)).re * (deriv (γ ∘ φ) t).im) =
      ∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im := by
  have hi := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := 1) (g := fun t => (γ t).re * (deriv γ t).im)
    (fun t _ => (hφ.differentiable one_ne_zero t).hasDerivAt)
    hφ.continuous_deriv_one.continuousOn
    ((Complex.continuous_re.comp hγ.continuous).mul
      (Complex.continuous_im.comp hγ.continuous_deriv_one))
  rw [hφ0, hφ1] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro t _
  change (γ (φ t)).re * (deriv (γ ∘ φ) t).im =
    ((γ (φ t)).re * (deriv γ (φ t)).im) * deriv φ t
  rw [deriv_reparam γ hγ φ hφ, Complex.smul_im, smul_eq_mul]
  ring

theorem signed_area_le_perimeter_approx (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (ε : ℝ) (hε : 0 < ε) :
    4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) ≤
      ((∫ t in (0 : ℝ)..1, ‖deriv γ t‖) + ε) ^ 2 := by
  let w := fun t => ‖deriv γ t‖ + ε
  have hw : Continuous w := hγ.continuous_deriv_one.norm.add continuous_const
  obtain ⟨φ, hφ, hm, hφ0, hφ1, hdφ⟩ := positive_density_reparametrization w hw ε hε
    (fun t => by dsimp only [w]; exact le_add_of_nonneg_left (norm_nonneg _))
  let L := (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) + ε
  have hLid : (∫ t in (0 : ℝ)..1, w t) = L := by
    rw [intervalIntegral.integral_add (hγ.continuous_deriv_one.norm.intervalIntegrable 0 1)
      intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul, L]
  have hL : 0 < L := by
    have hn := intervalIntegral.integral_nonneg_of_forall (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
      (fun t => norm_nonneg (deriv γ t))
    dsimp only [L]
    linarith
  have hwp (t : ℝ) : 0 < w t := by dsimp only [w]; positivity
  have hd (t : ℝ) : deriv (γ ∘ φ) t = (L / w (φ t)) • deriv γ (φ t) := by
    rw [deriv_reparam γ hγ φ hφ, (hdφ t).deriv, hLid]
  have hnorm (t : ℝ) : ‖deriv (γ ∘ φ) t‖ ≤ L := by
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hL (hwp _))]
    rw [div_mul_eq_mul_div, div_le_iff₀ (hwp _)]
    dsimp only [w]
    nlinarith
  have hδ : ContDiff ℝ 1 (γ ∘ φ) := hγ.comp hφ
  have hcδ : (γ ∘ φ) 0 = (γ ∘ φ) 1 := by simpa [hφ0, hφ1] using hclosed
  have hbound := signed_area_le_energy (fun t => ((γ ∘ φ) t).re)
    (fun t => ((γ ∘ φ) t).im) (Complex.reCLM.contDiff.comp hδ)
    (Complex.imCLM.contDiff.comp hδ) (congrArg Complex.re hcδ) (congrArg Complex.im hcδ)
  simp only [Green.deriv_re _ hδ, Green.deriv_im _ hδ] at hbound
  change 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ (φ t)).re * (deriv (γ ∘ φ) t).im) ≤ _ at hbound
  rw [reparam_signed_area γ hγ φ hφ hφ0 hφ1] at hbound
  have hie : IntervalIntegrable (fun t => (deriv (γ ∘ φ) t).re ^ 2 +
      (deriv (γ ∘ φ) t).im ^ 2) volume 0 1 :=
    (((Complex.continuous_re.comp hδ.continuous_deriv_one).pow 2).add
      ((Complex.continuous_im.comp hδ.continuous_deriv_one).pow 2)).intervalIntegrable 0 1
  apply hbound.trans
  calc
    _ ≤ ∫ _t in (0 : ℝ)..1, L ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) hie intervalIntegrable_const
      intro t _
      have hn : (deriv (γ ∘ φ) t).re ^ 2 + (deriv (γ ∘ φ) t).im ^ 2 =
          ‖deriv (γ ∘ φ) t‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, pow_two]
      rw [hn]
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm t) 2
    _ = L ^ 2 := by simp

/-- The sharp perimeter bound for every C¹ closed curve, with arbitrary speed. -/
theorem signed_area_le_perimeter (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) :
    4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) ≤
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
  let L := ∫ t in (0 : ℝ)..1, ‖deriv γ t‖
  have hlim : Tendsto (fun ε : ℝ => (L + ε) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (L ^ 2)) := by
    have hc : Continuous (fun ε : ℝ => (L + ε) ^ 2) :=
      (continuous_const.add continuous_id).pow 2
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact signed_area_le_perimeter_approx γ hγ hclosed ε hε

theorem jordan_isoperimetric_c1 (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
  rw [← Green.complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected
    hBoundary hCurve hClosed hSimple hPositive]
  exact signed_area_le_perimeter γ hCurve hClosed

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.signed_area_le_perimeter
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_c1

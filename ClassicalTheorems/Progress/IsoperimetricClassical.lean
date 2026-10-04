/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.Wirtinger
import ClassicalTheorems.Progress.GreenClassicalArea

/-! Sharp area bounds for C¹ Jordan curves, using Wirtinger and Green's theorem.
The smooth equality characterization is proved in `IsoperimetricEquality`.
The general rectifiable-curve extension remains open. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The signed area of a closed C¹ planar curve is bounded by its energy. -/
theorem signed_area_le_energy (x y : ℝ → ℝ) (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hxclosed : x 0 = x 1) (hyclosed : y 0 = y 1) :
    4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) ≤
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2 := by
  let m := ∫ t in (0 : ℝ)..1, x t
  let X := fun t => x t - m
  have hX : Continuous X := hx.continuous.sub continuous_const
  have hdx := hx.continuous_deriv_one
  have hdy := hy.continuous_deriv_one
  have hiX : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 :=
    (hX.pow 2).intervalIntegrable 0 1
  have hidx : IntervalIntegrable (fun t => deriv x t ^ 2) volume 0 1 :=
    (hdx.pow 2).intervalIntegrable 0 1
  have hidy : IntervalIntegrable (fun t => deriv y t ^ 2) volume 0 1 :=
    (hdy.pow 2).intervalIntegrable 0 1
  have hiy : (∫ t in (0 : ℝ)..1, deriv y t) = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hy.differentiable one_ne_zero t) (hdy.intervalIntegrable 0 1),
      hyclosed, sub_self]
  have harea : (∫ t in (0 : ℝ)..1, X t * deriv y t) =
      ∫ t in (0 : ℝ)..1, x t * deriv y t := by
    have hixy : IntervalIntegrable (fun t => x t * deriv y t) volume 0 1 :=
      (hx.continuous.mul hdy).intervalIntegrable 0 1
    have himy : IntervalIntegrable (fun t => m * deriv y t) volume 0 1 :=
      (hdy.intervalIntegrable 0 1).const_mul m
    simp only [X, sub_mul]
    rw [intervalIntegral.integral_sub hixy himy,
      intervalIntegral.integral_const_mul, hiy, mul_zero, sub_zero]
  have hbound :
      4 * Real.pi * (∫ t in (0 : ℝ)..1, X t * deriv y t) ≤
        4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) +
          (∫ t in (0 : ℝ)..1, deriv y t ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hiX.const_mul _) hidy]
    apply intervalIntegral.integral_mono_on (by norm_num)
      (((hX.mul hdy).intervalIntegrable 0 1).const_mul _)
      ((hiX.const_mul _).add hidy)
    intro t _
    change 4 * Real.pi * (X t * deriv y t) ≤ 4 * Real.pi ^ 2 * X t ^ 2 + deriv y t ^ 2
    nlinarith [sq_nonneg (2 * Real.pi * X t - deriv y t)]
  rw [harea] at hbound
  rw [intervalIntegral.integral_add hidx hidy]
  exact hbound.trans (add_le_add (wirtinger_centered x hx hxclosed) le_rfl)

/-- The classical sharp area bound for a C¹ positively oriented Jordan curve,
expressed first using its parameter energy. -/
theorem jordan_area_le_energy (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2 := by
  have h := signed_area_le_energy (fun t => (γ t).re) (fun t => (γ t).im)
    (Complex.reCLM.contDiff.comp hCurve) (Complex.imCLM.contDiff.comp hCurve)
    (congrArg Complex.re hClosed) (congrArg Complex.im hClosed)
  simp only [Green.deriv_re γ hCurve, Green.deriv_im γ hCurve] at h
  rw [Green.complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected
    hBoundary hCurve hClosed hSimple hPositive] at h
  convert h using 1
  apply intervalIntegral.integral_congr
  intro t _
  change ‖deriv γ t‖ ^ 2 = (deriv γ t).re ^ 2 + (deriv γ t).im ^ 2
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, pow_two]

/-- For a constant-speed C¹ Jordan boundary, the square of its perimeter is
at least four π times its geometric enclosed area. -/
theorem jordan_isoperimetric_constant_speed (D : Set ℂ) (γ : ℝ → ℂ) (L : ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hSpeed : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ = L) :
    (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) = L ∧
      4 * Real.pi * (volume D).toReal ≤ L ^ 2 := by
  have hi : (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) = L := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, L := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hSpeed t (by simpa using ht)
      _ = L := by simp
  refine ⟨hi, ?_⟩
  have he : (∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) = L ^ 2 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, L ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ‖deriv γ t‖ ^ 2 = L ^ 2
        rw [hSpeed t (by simpa using ht)]
      _ = L ^ 2 := by simp
  simpa only [he] using jordan_area_le_energy D γ hDomain hBounded hConnected
    hBoundary hCurve hClosed hSimple hPositive

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_area_le_energy
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_constant_speed

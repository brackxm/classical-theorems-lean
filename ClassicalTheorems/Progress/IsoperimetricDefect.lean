/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricC1

/-! Quantitative completed-square defects for the stationary-point equality
argument. Every estimate is independent of a nonvanishing-speed assumption. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem area_energy_defect_bound (x y : ℝ → ℝ) (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hxc : x 0 = x 1) (hyc : y 0 = y 1) :
    (∫ t in (0 : ℝ)..1,
      (2 * Real.pi * (x t - ∫ s in (0 : ℝ)..1, x s) - deriv y t) ^ 2) ≤
      (∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) := by
  let m := ∫ t in (0 : ℝ)..1, x t
  let X := fun t => x t - m
  have hX : Continuous X := hx.continuous.sub continuous_const
  have hdx := hx.continuous_deriv_one
  have hdy := hy.continuous_deriv_one
  have hiX : IntervalIntegrable (fun t => X t ^ 2) volume 0 1 := (hX.pow 2).intervalIntegrable 0 1
  have hidx : IntervalIntegrable (fun t => deriv x t ^ 2) volume 0 1 := (hdx.pow 2).intervalIntegrable 0 1
  have hidy : IntervalIntegrable (fun t => deriv y t ^ 2) volume 0 1 := (hdy.pow 2).intervalIntegrable 0 1
  have hixy : IntervalIntegrable (fun t => X t * deriv y t) volume 0 1 := (hX.mul hdy).intervalIntegrable 0 1
  have harea : (∫ t in (0 : ℝ)..1, X t * deriv y t) = ∫ t in (0 : ℝ)..1, x t * deriv y t := by
    have hiy : (∫ t in (0 : ℝ)..1, deriv y t) = 0 := by
      rw [intervalIntegral.integral_deriv_eq_sub
        (fun t _ => hy.differentiable one_ne_zero t) (hdy.intervalIntegrable 0 1), hyc, sub_self]
    have hi : IntervalIntegrable (fun t => x t * deriv y t) volume 0 1 :=
      (hx.continuous.mul hdy).intervalIntegrable 0 1
    have hi' : IntervalIntegrable (fun t => m * deriv y t) volume 0 1 :=
      (hdy.intervalIntegrable 0 1).const_mul m
    simp only [X, sub_mul]
    rw [intervalIntegral.integral_sub hi hi', intervalIntegral.integral_const_mul,
      hiy, mul_zero, sub_zero]
  have hid : (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) =
      4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) +
        (∫ t in (0 : ℝ)..1, deriv y t ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1, (4 * Real.pi ^ 2 * X t ^ 2 + deriv y t ^ 2) -
          4 * Real.pi * (X t * deriv y t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hiX.const_mul _).add hidy) (hixy.const_mul _),
          intervalIntegral.integral_add (hiX.const_mul _) hidy,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, harea]
  change (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) ≤ _
  rw [hid, intervalIntegral.integral_add hidx hidy]
  have hw := wirtinger_centered x hx hxc
  change 4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) ≤ _ at hw
  linarith

theorem density_reparam_mean (x w φ : ℝ → ℝ) (hx : Continuous x) (hw : Continuous w)
    (hφ : ContDiff ℝ 1 φ) (hφ0 : φ 0 = 0) (hφ1 : φ 1 = 1) (L : ℝ)
    (hL : L ≠ 0) (hwp : ∀ t, 0 < w t)
    (hdφ : ∀ t, HasDerivAt φ (L / w (φ t)) t) :
    (∫ t in (0 : ℝ)..1, x (φ t)) = (∫ t in (0 : ℝ)..1, x t * w t) / L := by
  have hi := intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1)
    (g := fun t => x t * w t) (fun t _ => hdφ t)
    (hφ.continuous_deriv_one.continuousOn.congr (fun t _ => (hdφ t).deriv.symm)) (hx.mul hw)
  rw [hφ0, hφ1] at hi
  have hid : (∫ t in (0 : ℝ)..1, x t * w t) = L * ∫ t in (0 : ℝ)..1, x (φ t) := by
    rw [← hi, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    change (x (φ t) * w (φ t)) * (L / w (φ t)) = L * x (φ t)
    field_simp [(hwp (φ t)).ne']
  rw [hid]
  field_simp

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.area_energy_defect_bound

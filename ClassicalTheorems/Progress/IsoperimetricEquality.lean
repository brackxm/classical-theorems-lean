/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricClassical
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! Equality in the smooth isoperimetric inequality forces a circle.
The proof uses both coordinate versions of the completed-square bound. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem continuous_sq_zero_of_integral_le_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hi : (∫ t in (0 : ℝ)..1, f t ^ 2) ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, f t = 0 := by
  intro t ht
  by_contra h
  have hp := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    (hf.pow 2).continuousOn (fun s _ => sq_nonneg (f s))
    ⟨t, ht, sq_pos_of_ne_zero h⟩
  change 0 < ∫ t in (0 : ℝ)..1, f t ^ 2 at hp
  linarith

/-- Equality in the area-energy bound forces the derivative relation for one coordinate. -/
theorem area_energy_equality_coordinate (x y : ℝ → ℝ) (hx : ContDiff ℝ 1 x)
    (hy : ContDiff ℝ 1 y) (hxclosed : x 0 = x 1) (hyclosed : y 0 = y 1)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) =
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      deriv y t = 2 * Real.pi * (x t - ∫ s in (0 : ℝ)..1, x s) := by
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
  have hixy : IntervalIntegrable (fun t => X t * deriv y t) volume 0 1 :=
    (hX.mul hdy).intervalIntegrable 0 1
  have harea : (∫ t in (0 : ℝ)..1, X t * deriv y t) =
      ∫ t in (0 : ℝ)..1, x t * deriv y t := by
    have hiy : (∫ t in (0 : ℝ)..1, deriv y t) = 0 := by
      rw [intervalIntegral.integral_deriv_eq_sub
        (fun t _ => hy.differentiable one_ne_zero t) (hdy.intervalIntegrable 0 1),
        hyclosed, sub_self]
    have hi : IntervalIntegrable (fun t => x t * deriv y t) volume 0 1 :=
      (hx.continuous.mul hdy).intervalIntegrable 0 1
    have hi' : IntervalIntegrable (fun t => m * deriv y t) volume 0 1 :=
      (hdy.intervalIntegrable 0 1).const_mul m
    simp only [X, sub_mul]
    rw [intervalIntegral.integral_sub hi hi', intervalIntegral.integral_const_mul,
      hiy, mul_zero, sub_zero]
  have hidentity : (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) =
      4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) +
        (∫ t in (0 : ℝ)..1, deriv y t ^ 2) -
        4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) := by
    calc
      _ = ∫ t in (0 : ℝ)..1,
          (4 * Real.pi ^ 2 * X t ^ 2 + deriv y t ^ 2) -
            4 * Real.pi * (X t * deriv y t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub ((hiX.const_mul _).add hidy) (hixy.const_mul _),
          intervalIntegral.integral_add (hiX.const_mul _) hidy,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, harea]
  have hzero : ∀ t ∈ Icc (0 : ℝ) 1, 2 * Real.pi * X t - deriv y t = 0 := by
    apply continuous_sq_zero_of_integral_le_zero _ ((continuous_const.mul hX).sub hdy)
    change (∫ t in (0 : ℝ)..1, (2 * Real.pi * X t - deriv y t) ^ 2) ≤ 0
    rw [hidentity, heq, intervalIntegral.integral_add hidx hidy]
    have hw := wirtinger_centered x hx hxclosed
    change 4 * Real.pi ^ 2 * (∫ t in (0 : ℝ)..1, X t ^ 2) ≤ _ at hw
    linarith
  intro t ht
  exact (sub_eq_zero.mp (hzero t ht)).symm

/-- Equality makes the centered curve satisfy the circle's rotation ODE. -/
theorem area_energy_equality_ode (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) :
    ∃ c : ℂ, ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * (γ t - c) := by
  let x := fun t => (γ t).re
  let y := fun t => (γ t).im
  have hx : ContDiff ℝ 1 x := Complex.reCLM.contDiff.comp hγ
  have hy : ContDiff ℝ 1 y := Complex.imCLM.contDiff.comp hγ
  have hxc : x 0 = x 1 := congrArg Complex.re hclosed
  have hyc : y 0 = y 1 := congrArg Complex.im hclosed
  have hdX (t : ℝ) : deriv x t = (deriv γ t).re := Green.deriv_re γ hγ t
  have hdY (t : ℝ) : deriv y t = (deriv γ t).im := Green.deriv_im γ hγ t
  have he : 4 * Real.pi * (∫ t in (0 : ℝ)..1, x t * deriv y t) =
      ∫ t in (0 : ℝ)..1, deriv x t ^ 2 + deriv y t ^ 2 := by
    simp only [hdX, hdY]
    convert heq using 1
    apply intervalIntegral.integral_congr
    intro t _
    change (deriv γ t).re ^ 2 + (deriv γ t).im ^ 2 = ‖deriv γ t‖ ^ 2
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, pow_two]
  have hb := area_energy_equality_coordinate x y hx hy hxc hyc he
  have hibp : (∫ t in (0 : ℝ)..1, y t * deriv x t) =
      -(∫ t in (0 : ℝ)..1, x t * deriv y t) := by
    rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t _ => (hy.differentiable one_ne_zero t).hasDerivAt)
      (fun t _ => (hx.differentiable one_ne_zero t).hasDerivAt)
      (hy.continuous_deriv_one.intervalIntegrable 0 1)
      (hx.continuous_deriv_one.intervalIntegrable 0 1), hyc, hxc, sub_self, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  have he' : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (-y t) * deriv x t) =
      ∫ t in (0 : ℝ)..1, deriv (fun s => -y s) t ^ 2 + deriv x t ^ 2 := by
    have hdneg (t : ℝ) : deriv (fun s => -y s) t = -deriv y t :=
      (hy.differentiable one_ne_zero t).hasDerivAt.neg.deriv
    simp only [hdneg, neg_sq, neg_mul, intervalIntegral.integral_neg, hibp, neg_neg]
    rw [he]
    apply intervalIntegral.integral_congr
    intro t _
    change deriv x t ^ 2 + deriv y t ^ 2 = deriv y t ^ 2 + deriv x t ^ 2
    ring
  have ha := area_energy_equality_coordinate (fun t => -y t) x hy.neg hx
    (congrArg Neg.neg hyc) hxc he'
  refine ⟨⟨∫ t in (0 : ℝ)..1, x t, ∫ t in (0 : ℝ)..1, y t⟩, ?_⟩
  intro t ht
  apply Complex.ext
  · have ha' := ha t ht
    simp only [intervalIntegral.integral_neg] at ha'
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      mul_zero, sub_zero, zero_sub, mul_one, add_zero]
    norm_num
    rw [← hdX]
    dsimp only [y] at ha'
    linarith
  · have hb' := hb t ht
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im,
      mul_zero, sub_zero, zero_sub, mul_one, add_zero, zero_add]
    norm_num
    rw [← hdY]
    exact hb'

/-- Solve the rotation equation on the whole closed parameter interval. -/
theorem rotation_ode_solution (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (c : ℂ)
    (hode : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * (γ t - c)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      γ t = c + Complex.exp ((2 * Real.pi * Complex.I) * t) * (γ 0 - c) := by
  let k : ℂ := 2 * Real.pi * Complex.I
  let F : ℝ → ℂ := fun t => Complex.exp (-k * t) * (γ t - c)
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F 0 t := by
    have hr : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using! Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := t)
    have hd := ((hr.const_mul (-k)).cexp).mul
      ((hγ.differentiable one_ne_zero t).hasDerivAt.sub_const c)
    convert hd using 1
    rw [hode t ht]
    dsimp only [k]
    ring
  intro t ht
  have hnorm := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun s hs => (hF s hs).differentiableAt)
    (fun s hs => by simp only [(hF s hs).deriv, norm_zero, le_refl])
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  have he : F t = F 0 := by
    simp only [zero_mul] at hnorm
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    simpa using le_antisymm hnorm (norm_nonneg (F t - F 0))
  have hm := congrArg (fun z => Complex.exp (k * t) * z) he
  dsimp only [F] at hm
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hm
  rw [← mul_assoc, ← Complex.exp_add] at hm
  have hc : k * (t : ℂ) + -k * t = 0 := by ring
  rw [hc, Complex.exp_zero, one_mul] at hm
  dsimp only [k] at hm
  linear_combination hm

/-- One complete unit rotation covers the unit circle. -/
theorem unit_rotation_image :
    (fun t : ℝ => Complex.exp ((2 * Real.pi * Complex.I) * t)) '' Icc 0 1 =
      Metric.sphere (0 : ℂ) 1 := by
  have hform (t : ℝ) : Complex.exp ((2 * Real.pi * Complex.I) * t) =
      circleMap 0 1 (2 * Real.pi * t) := by
    simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
    congr 1
    push_cast
    ring
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    change Complex.exp ((2 * Real.pi * Complex.I) * t) ∈ Metric.sphere (0 : ℂ) 1
    rw [hform]
    exact circleMap_mem_sphere 0 (by norm_num) _
  · intro z hz
    have hz' : z ∈ circleMap 0 1 '' Ioc 0 (2 * Real.pi) := by
      simpa only [image_circleMap_Ioc, abs_one] using hz
    obtain ⟨θ, hθ, rfl⟩ := hz'
    refine ⟨θ / (2 * Real.pi), ⟨div_nonneg hθ.1.le (by positivity), ?_⟩, ?_⟩
    · exact (div_le_one (by positivity)).2 hθ.2
    · change Complex.exp ((2 * Real.pi * Complex.I) * ((θ / (2 * Real.pi) : ℝ) : ℂ)) = _
      rw [hform]
      congr 1
      field_simp

/-- A nonconstant solution of the rotation equation traces exactly a circle. -/
theorem rotation_ode_image (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (c : ℂ)
    (hode : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * (γ t - c))
    (hv : γ 0 - c ≠ 0) : γ '' Icc 0 1 = Metric.sphere c ‖γ 0 - c‖ := by
  let v := γ 0 - c
  have hparam := rotation_ode_solution γ hγ c hode
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    rw [hparam t ht, Metric.mem_sphere, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_mul]
    have hunit : ‖Complex.exp ((2 * Real.pi * Complex.I) * t)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (unit_rotation_image ▸ ⟨t, ht, rfl⟩)
    rw [hunit, one_mul]
  · intro z hz
    have hdist : ‖z - c‖ = ‖v‖ := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hw : (z - c) / v ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, hdist, div_self]
      exact norm_ne_zero_iff.mpr hv
    rw [← unit_rotation_image] at hw
    obtain ⟨t, ht, he⟩ := hw
    change Complex.exp ((2 * Real.pi * Complex.I) * t) = (z - c) / v at he
    refine ⟨t, ht, ?_⟩
    rw [hparam t ht, he]
    dsimp only [v]
    rw [div_mul_cancel₀ _ hv]
    ring

/-- A simple closed C¹ curve attaining the area-energy bound is a circle. -/
theorem area_energy_equality_circle (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hsimple : InjOn γ (Ico 0 1))
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc 0 1 = Metric.sphere c r := by
  obtain ⟨c, hc⟩ := area_energy_equality_ode γ hγ hclosed heq
  have hv : γ 0 - c ≠ 0 := by
    intro hz
    have hparam := rotation_ode_solution γ hγ c hc
    have hhalf : γ (1 / 2) = γ 0 := by
      rw [hparam (1 / 2) (by norm_num), hz, mul_zero, add_zero]
      exact (sub_eq_zero.mp hz).symm
    have hbad := hsimple (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)
      (by norm_num : (0 : ℝ) ∈ Ico 0 1) hhalf
    norm_num at hbad
  exact ⟨c, ‖γ 0 - c‖, norm_pos_iff.mpr hv, rotation_ode_image γ hγ c hc hv⟩

/-- Equality in the smooth constant-speed isoperimetric bound forces the
actual boundary image to be a circle of positive radius. -/
theorem jordan_isoperimetric_equality_circle (D : Set ℂ) (γ : ℝ → ℂ) (L : ℝ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi)
    (hSpeed : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ = L)
    (hEquality : 4 * Real.pi * (volume D).toReal = L ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r := by
  have he : (∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2) = L ^ 2 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, L ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ‖deriv γ t‖ ^ 2 = L ^ 2
        rw [hSpeed t (by simpa using ht)]
      _ = L ^ 2 := by simp
  have ha : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv γ t‖ ^ 2 := by
    rw [Green.complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected
      hBoundary hCurve hClosed hSimple hPositive, he, hEquality]
  obtain ⟨c, r, hr, hcircle⟩ := area_energy_equality_circle γ hCurve hClosed hSimple ha
  exact ⟨c, r, hr, hBoundary.trans hcircle⟩

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.area_energy_equality_ode
#check_upstream ClassicalTheorems.Progress.Isoperimetric.rotation_ode_image
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_equality_circle

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricStationary

/-! Circle rigidity for arbitrary C¹ Jordan parametrizations, with stationary
points allowed. Equality gives a rotation equation with the arc-length clock. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem simple_curveLength_pos (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hsimple : InjOn γ (Ico 0 1)) : 0 < curveLength γ := by
  by_contra h
  have hL : curveLength γ ≤ 0 := le_of_not_gt h
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t = 0 := by
    intro t ht
    by_contra hd
    have hp := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
      hγ.continuous_deriv_one.norm.continuousOn (fun s _ => norm_nonneg _)
      ⟨t, ht, norm_pos_iff.mpr hd⟩
    change 0 < curveLength γ at hp
    linarith
  have hn := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun t _ => hγ.differentiable one_ne_zero t)
    (fun t ht => by simp only [hz t ht, norm_zero, le_refl])
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  have he : γ (1 / 2) = γ 0 := by
    simp only [zero_mul] at hn
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    exact le_antisymm hn (norm_nonneg _)
  have hb := hsimple (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)
    (by norm_num : (0 : ℝ) ∈ Ico 0 1) he
  norm_num at hb

theorem perimeter_equality_weighted_ode (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hL : 0 < curveLength γ)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) = curveLength γ ^ 2) :
    ∃ c : ℂ, ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * (‖deriv γ t‖ / curveLength γ) * (γ t - c) := by
  let β : ℝ → ℂ := fun t => Complex.I * γ t
  have hβ : ContDiff ℝ 1 β := contDiff_const.mul hγ
  have hbclosed : β 0 = β 1 := congrArg (fun z => Complex.I * z) hclosed
  have hbd (t : ℝ) : deriv β t = Complex.I * deriv γ t :=
    ((hγ.differentiable one_ne_zero t).hasDerivAt.const_mul Complex.I).deriv
  have hbn (t : ℝ) : ‖deriv β t‖ = ‖deriv γ t‖ := by rw [hbd, norm_mul, Complex.norm_I, one_mul]
  have hbr (t : ℝ) : (β t).re = -(γ t).im := by simp [β, Complex.mul_re]
  have hbdi (t : ℝ) : (deriv β t).im = (deriv γ t).re := by rw [hbd]; simp [Complex.mul_im]
  have hbL : curveLength β = curveLength γ := by
    unfold curveLength
    apply intervalIntegral.integral_congr
    intro t _
    exact hbn t
  have hibp : (∫ t in (0 : ℝ)..1, (γ t).im * (deriv γ t).re) =
      -(∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) := by
    have hx : ContDiff ℝ 1 (fun t => (γ t).re) := Complex.reCLM.contDiff.comp hγ
    have hy : ContDiff ℝ 1 (fun t => (γ t).im) := Complex.imCLM.contDiff.comp hγ
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (fun t _ => (hy.differentiable one_ne_zero t).hasDerivAt)
      (fun t _ => (hx.differentiable one_ne_zero t).hasDerivAt)
      (hy.continuous_deriv_one.intervalIntegrable 0 1) (hx.continuous_deriv_one.intervalIntegrable 0 1)
    simp only [Green.deriv_re γ hγ, Green.deriv_im γ hγ, hclosed, sub_self, zero_sub] at h
    rw [h]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  have hbeq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (β t).re * (deriv β t).im) = curveLength β ^ 2 := by
    simp only [hbr, hbdi, hbL, neg_mul, intervalIntegral.integral_neg, hibp, neg_neg]
    exact heq
  have ha := speedDefect_zero γ hγ hclosed hL heq
  have hb := speedDefect_zero β hβ hbclosed (by rwa [hbL]) hbeq
  let c : ℂ := ⟨weightedCoordMean γ 0, -weightedCoordMean β 0⟩
  refine ⟨c, ?_⟩
  intro t ht
  have hai := ha t ht
  have hbi := hb t ht
  simp only [speedDefect, add_zero, hbL, hbn, hbr, hbdi] at hai hbi
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, c]
    norm_num
    field_simp [hL.ne']
    nlinarith [hbi]
  · simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, c]
    norm_num
    field_simp [hL.ne']
    nlinarith [hai]

/-- Solve rotation with an arbitrary C¹ clock. The clock may stop. -/
theorem clock_rotation_solution (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) (hu0 : u 0 = 0) (c : ℂ)
    (hode : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * deriv u t * (γ t - c)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      γ t = c + Complex.exp ((2 * Real.pi * Complex.I) * u t) * (γ 0 - c) := by
  let k : ℂ := 2 * Real.pi * Complex.I
  let F := fun t => Complex.exp (-k * u t) * (γ t - c)
  have hF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt F 0 t := by
    have hr : HasDerivAt (fun s => (u s : ℂ)) ((deriv u t : ℝ) : ℂ) t := by
      simpa using! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        (hu.differentiable one_ne_zero t).hasDerivAt
    have hd := ((hr.const_mul (-k)).cexp).mul
      ((hγ.differentiable one_ne_zero t).hasDerivAt.sub_const c)
    convert hd using 1
    rw [hode t ht]
    dsimp only [k]
    ring
  intro t ht
  have hn := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun s hs => (hF s hs).differentiableAt)
    (fun s hs => by simp only [(hF s hs).deriv, norm_zero, le_refl])
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  have he : F t = F 0 := by
    simp only [zero_mul] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  have hm := congrArg (fun z => Complex.exp (k * u t) * z) he
  dsimp only [F] at hm
  simp only [hu0, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at hm
  rw [← mul_assoc, ← Complex.exp_add] at hm
  have hc : k * (u t : ℂ) + -k * u t = 0 := by ring
  rw [hc, Complex.exp_zero, one_mul] at hm
  dsimp only [k] at hm
  linear_combination hm

theorem circle_image_of_clock (γ : ℝ → ℂ) (u : ℝ → ℝ) (c : ℂ)
    (himage : u '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1)
    (hparam : ∀ t ∈ Icc (0 : ℝ) 1,
      γ t = c + Complex.exp ((2 * Real.pi * Complex.I) * u t) * (γ 0 - c))
    (hv : γ 0 - c ≠ 0) : γ '' Icc 0 1 = Metric.sphere c ‖γ 0 - c‖ := by
  let v := γ 0 - c
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    have hut : u t ∈ Icc (0 : ℝ) 1 := himage ▸ mem_image_of_mem u ht
    rw [hparam t ht, Metric.mem_sphere, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_mul]
    have hn : ‖Complex.exp ((2 * Real.pi * Complex.I) * u t)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (unit_rotation_image ▸ ⟨u t, hut, rfl⟩)
    rw [hn, one_mul]
  · intro z hz
    have hd : ‖z - c‖ = ‖v‖ := by simpa only [Metric.mem_sphere, dist_eq_norm] using hz
    have hw : (z - c) / v ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, hd, div_self]
      exact norm_ne_zero_iff.mpr hv
    rw [← unit_rotation_image] at hw
    obtain ⟨θ, hθ, heθ⟩ := hw
    have hθ' : θ ∈ u '' Icc (0 : ℝ) 1 := himage.symm ▸ hθ
    obtain ⟨t, ht, hut⟩ := hθ'
    refine ⟨t, ht, ?_⟩
    change Complex.exp ((2 * Real.pi * Complex.I) * θ) = (z - c) / v at heθ
    rw [hparam t ht, hut, heθ]
    dsimp only [v]
    rw [div_mul_cancel₀ _ hv]
    ring

/-- Circle rigidity for every simple closed C¹ curve, with zero speed allowed. -/
theorem perimeter_equality_circle_c1 (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hsimple : InjOn γ (Ico 0 1))
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) = curveLength γ ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc 0 1 = Metric.sphere c r := by
  have hL := simple_curveLength_pos γ hγ hsimple
  obtain ⟨c, hc⟩ := perimeter_equality_weighted_ode γ hγ hclosed hL heq
  let u := fun t => (∫ s in (0 : ℝ)..t, ‖deriv γ s‖) / curveLength γ
  have hdu (t : ℝ) : HasDerivAt u (‖deriv γ t‖ / curveLength γ) t :=
    (hγ.continuous_deriv_one.norm.integral_hasStrictDerivAt 0 t).hasDerivAt.div_const _
  have hu : ContDiff ℝ 1 u := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun t => (hdu t).differentiableAt, ?_⟩
    have he : deriv u = fun t => ‖deriv γ t‖ / curveLength γ := funext (fun t => (hdu t).deriv)
    rw [he]
    exact hγ.continuous_deriv_one.norm.div_const _
  have hu0 : u 0 = 0 := by simp [u]
  have hu1 : u 1 = 1 := by
    change curveLength γ / curveLength γ = 1
    exact div_self hL.ne'
  have humono : Monotone u := monotone_of_deriv_nonneg (fun t => (hdu t).differentiableAt)
    (fun t => by rw [(hdu t).deriv]; exact div_nonneg (norm_nonneg _) hL.le)
  have himage : u '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hu.continuous.continuousOn.image_Icc_of_monotoneOn (by norm_num) (humono.monotoneOn _), hu0, hu1]
  have hode : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv γ t = (2 * Real.pi * Complex.I) * deriv u t * (γ t - c) := by
    intro t ht
    rw [(hdu t).deriv]
    simpa only [Complex.ofReal_div] using hc t ht
  have hparam := clock_rotation_solution γ hγ u hu hu0 c hode
  have hv : γ 0 - c ≠ 0 := by
    intro hz
    have he : γ (1 / 2) = γ 0 := by
      rw [hparam (1 / 2) (by norm_num), hz, mul_zero, add_zero]
      exact (sub_eq_zero.mp hz).symm
    have hb := hsimple (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)
      (by norm_num : (0 : ℝ) ∈ Ico 0 1) he
    norm_num at hb
  exact ⟨c, ‖γ 0 - c‖, norm_pos_iff.mpr hv, circle_image_of_clock γ u c himage hparam hv⟩

/-- The geometric bound and circle rigidity, including stationary C¹ points. -/
theorem jordan_isoperimetric_c1_complete (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 ∧
      (4 * Real.pi * (volume D).toReal = (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r) := by
  refine ⟨jordan_isoperimetric_c1 D γ hDomain hBounded hConnected hBoundary
    hCurve hClosed hSimple hPositive, ?_⟩
  intro heq
  have he : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      curveLength γ ^ 2 := by
    unfold curveLength
    rwa [Green.complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected
      hBoundary hCurve hClosed hSimple hPositive]
  obtain ⟨c, r, hr, hcircle⟩ := perimeter_equality_circle_c1 γ hCurve hClosed hSimple he
  exact ⟨c, r, hr, hBoundary.trans hcircle⟩

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.perimeter_equality_circle_c1
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_c1_complete

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.GreenArea
import MovingSofa.Curve.Jordan.SignedArea

/-! Verified results for the area step of Green’s theorem. The full arbitrary-field identity
is proved in `ClassicalTheorems.Progress.GreenFull`. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Green

/-- Winding as an ordinary derivative integral for a simple closed C¹ planar path. -/
theorem c1_curveWinding_integral (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hinj : InjOn γ (Ico 0 1)) (p : Point)
    (hp : p ∉ γ '' Icc 0 1) :
    2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => γ t) p =
      (∫ t in (0 : ℝ)..1, windingKernel (γ t) p 0 * deriv (fun s => γ s 1) t) -
      (∫ t in (0 : ℝ)..1, windingKernel (γ t) p 1 * deriv (fun s => γ s 0) t) := by
  let x := c1BVPath γ hγ
  have hxc : x.val ⟨0, le_rfl, by norm_num⟩ = x.val ⟨1, by norm_num, le_rfl⟩ := hclosed
  have hxi : InjOn x.val {t | (t : ℝ) < 1} := by
    intro s hs t ht heq
    apply Subtype.ext
    exact hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq
  have hp' : p ∉ range x.val := by
    rintro ⟨t, heq⟩
    exact hp ⟨t, t.property, heq⟩
  have hw := ((jordanBV_winding_integral 0 1 (by norm_num) x hxc hxi).2.1 p hp').2
  have hq (i : Fin 2) : ContinuousOn (fun t => windingKernel (γ t) p i) (Icc 0 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (windingKernel_coord_continuous_bounded x.property.1 hp' i).1
  change 2 * Real.pi * curveWinding _ (fun t : Icc (0 : ℝ) 1 => γ t) p =
    intervalStieltjesIntegral (continuousBVCoordinate (c1BVPath γ hγ) 1)
      (fun t => windingKernel (γ t) p 0) univ -
    intervalStieltjesIntegral (continuousBVCoordinate (c1BVPath γ hγ) 0)
      (fun t => windingKernel (γ t) p 1) univ at hw
  rw [c1BVPath_stieltjes_integral γ hγ 1 _ (hq 0),
    c1BVPath_stieltjes_integral γ hγ 0 _ (hq 1)] at hw
  exact hw

/-- Complex coordinates preserve the inverse-distance winding integrand. -/
theorem windingKernel_complex (z p v : ℂ) :
    windingKernel (Complex.orthonormalBasisOneI.repr z)
      (Complex.orthonormalBasisOneI.repr p) 0 * v.im -
    windingKernel (Complex.orthonormalBasisOneI.repr z)
      (Complex.orthonormalBasisOneI.repr p) 1 * v.re = (v / (z - p)).im := by
  have hn : ‖Complex.orthonormalBasisOneI.repr z -
      Complex.orthonormalBasisOneI.repr p‖ ^ 2 = Complex.normSq (z - p) := by
    rw [← map_sub, LinearIsometryEquiv.norm_map, Complex.normSq_eq_norm_sq]
  simp only [windingKernel, PiLp.smul_apply, smul_eq_mul]
  rw [hn]
  simp only [PiLp.sub_apply, Complex.orthonormalBasisOneI_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Complex.div_im,
    Complex.sub_re, Complex.sub_im]
  ring

theorem deriv_re (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (t : ℝ) :
    deriv (fun s => (γ s).re) t = (deriv γ t).re :=
  (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hγ.differentiable one_ne_zero t).hasDerivAt).deriv

theorem deriv_im (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (t : ℝ) :
    deriv (fun s => (γ s).im) t = (deriv γ t).im :=
  (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
    (hγ.differentiable one_ne_zero t).hasDerivAt).deriv


/-- The winding integral used in Green’s theorem equals the angle-lift winding used by
our Jordan-area dependency, for the same simple closed C¹ curve. -/
theorem complex_curveWinding_integral (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hinj : InjOn γ (Ico 0 1)) (p : ℂ)
    (hp : p ∉ γ '' Icc 0 1) :
    2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (γ t))
      (Complex.orthonormalBasisOneI.repr p) =
      ∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - p)).im := by
  let e := Complex.orthonormalBasisOneI.repr
  let δ : ℝ → Point := e ∘ γ
  have hd : ContDiff ℝ 1 δ := e.toContinuousLinearMap.contDiff.comp hγ
  have hclosed' : δ 0 = δ 1 := congrArg e hclosed
  have hinj' : InjOn δ (Ico 0 1) := e.injective.comp_injOn hinj
  have hp' : e p ∉ δ '' Icc 0 1 := by
    rintro ⟨t, ht, heq⟩
    exact hp ⟨t, ht, e.injective heq⟩
  have hq (i : Fin 2) : ContinuousOn (fun t => windingKernel (δ t) (e p) i) (Icc 0 1) :=
    continuousOn_iff_continuous_domRestrict.mpr
      (windingKernel_coord_continuous_bounded
        (hd.continuous.comp continuous_subtype_val)
        (by rintro ⟨t, heq⟩; exact hp' ⟨t, t.property, heq⟩) i).1
  have hdcoord (i : Fin 2) : Continuous (deriv (fun s => δ s i)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hd).continuous_deriv_one
  have hi (i j : Fin 2) : IntervalIntegrable
      (fun t => windingKernel (δ t) (e p) i * deriv (fun s => δ s j) t) volume 0 1 :=
    ((hq i).mul (hdcoord j).continuousOn).intervalIntegrable_of_Icc (by norm_num)
  change 2 * Real.pi * curveWinding (by norm_num : (0 : ℝ) ≤ 1)
    (fun t : Icc (0 : ℝ) 1 => δ t) (e p) = _
  rw [c1_curveWinding_integral δ hd hclosed' hinj' (e p) hp',
    ← intervalIntegral.integral_sub (hi 0 1) (hi 1 0)]
  apply intervalIntegral.integral_congr
  intro t _
  have hd0 : deriv (fun s => δ s 0) t = (deriv γ t).re := by
    simpa [δ, e] using deriv_re γ hγ t
  have hd1 : deriv (fun s => δ s 1) t = (deriv γ t).im := by
    simpa [δ, e] using deriv_im γ hγ t
  change windingKernel (δ t) (e p) 0 * deriv (fun s => δ s 1) t -
    windingKernel (δ t) (e p) 1 * deriv (fun s => δ s 0) t = _
  rw [hd0, hd1]
  exact windingKernel_complex (γ t) p (deriv γ t)

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.c1_curveWinding_integral
#check_upstream ClassicalTheorems.Progress.Green.windingKernel_complex
#check_upstream ClassicalTheorems.Progress.Green.deriv_re
#check_upstream ClassicalTheorems.Progress.Green.deriv_im

#check_upstream ClassicalTheorems.Progress.Green.complex_curveWinding_integral

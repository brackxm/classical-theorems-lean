/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.CircleOptimality

/-! Simplicity and winding force a continuous angular lift of a Jordan circle
to traverse exactly one turn. This bounds every such parametrization's perimeter. -/

noncomputable section
open MeasureTheory Set MovingSofa
open scoped ENNReal
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A lift distinguishing the two endpoints of a simple closed path is injective. -/
theorem simple_closed_lift_injective (x : Icc (0 : ℝ) 1 → Point)
    (θ : Icc (0 : ℝ) 1 → ℝ)
    (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1})
    (hlift : ∀ s t, θ s = θ t → x s = x t)
    (hne : θ ⟨0, by norm_num⟩ ≠ θ ⟨1, by norm_num⟩) :
    Function.Injective θ := by
  intro s t hst
  have hlt (u : Icc (0 : ℝ) 1) (hu : u ≠ ⟨1, by norm_num⟩) : (u : ℝ) < 1 :=
    lt_of_le_of_ne u.property.2 (fun h => hu (Subtype.ext h))
  have he := hlift s t hst
  by_cases hs1 : s = ⟨1, by norm_num⟩
  · subst s
    by_cases ht1 : t = ⟨1, by norm_num⟩
    · exact ht1.symm
    · have ht0 := hinj (x₁ := ⟨0, by norm_num⟩) (x₂ := t)
        (by norm_num) (hlt t ht1) (hclosed.trans he)
      exact False.elim (hne ((congrArg θ ht0).trans hst.symm))
  · by_cases ht1 : t = ⟨1, by norm_num⟩
    · subst t
      have hs0 := hinj (x₁ := s) (x₂ := ⟨0, by norm_num⟩)
        (hlt s hs1) (by norm_num) (he.trans hclosed.symm)
      exact False.elim (hne ((congrArg θ hs0).symm.trans hst))
    · exact hinj (hlt s hs1) (hlt t ht1) he

/-- A positively oriented Jordan parametrization of a circle has a strictly
increasing angle lift whose endpoint increment is exactly `2π`. -/
theorem circle_monotone_angle (x : Icc (0 : ℝ) 1 → Point) (c : Point) (r : ℝ)
    (hr : 0 < r)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (Metric.sphere c r) true x) :
    ∃ θ : Icc (0 : ℝ) 1 → ℝ, StrictMono θ ∧
      θ ⟨1, by norm_num⟩ - θ ⟨0, by norm_num⟩ = 2 * Real.pi ∧
      ∀ t, x t = c + r •
        Complex.orthonormalBasisOneI.repr (Real.cos (θ t) + Real.sin (θ t) * Complex.I) := by
  let : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
  have hc : c ∈ jordanInterior (Metric.sphere c r) :=
    ball_subset_jordanInterior_sphere c r (Metric.mem_ball_self hr)
  have hw : curveWinding (by norm_num : (0 : ℝ) ≤ 1) x c = 1 := by
    simpa using hx.2.2.2.2.2.2 c hc
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero
    (by norm_num : (0 : ℝ) ≤ 1) (by rw [hw]; norm_num)
  have hdiff : θ ⟨1, by norm_num⟩ - θ ⟨0, by norm_num⟩ = 2 * Real.pi := by
    rw [hθ.curveWinding_eq (by norm_num)] at hw
    exact (div_eq_iff (by positivity : 2 * Real.pi ≠ 0)).mp hw |>.trans (one_mul _)
  have hrepr (t : Icc (0 : ℝ) 1) : x t = c + r •
      Complex.orthonormalBasisOneI.repr (Real.cos (θ t) + Real.sin (θ t) * Complex.I) := by
    have ht : x t ∈ Metric.sphere c r := hx.2.2.2.1 ▸ mem_range_self t
    have hnorm : ‖x t - c‖ = r := mem_sphere_iff_norm.mp ht
    have hc0 := (hθ.2 t).1
    have hc1 := (hθ.2 t).2
    rw [hnorm] at hc0 hc1
    have he0 := (eq_div_iff hr.ne').mp hc0
    have he1 := (eq_div_iff hr.ne').mp hc1
    ext i
    fin_cases i <;>
      simp [Complex.orthonormalBasisOneI_repr_apply, Complex.mul_re, Complex.mul_im]
    · change x t 0 = c 0 + r * Real.cos (θ t)
      change Real.cos (θ t) * r = x t 0 - c 0 at he0
      nlinarith
    · change x t 1 = c 1 + r * Real.sin (θ t)
      change Real.sin (θ t) * r = x t 1 - c 1 at he1
      nlinarith
  have hi : Function.Injective θ := simple_closed_lift_injective x θ
    hx.2.2.2.2.1 hx.2.2.2.2.2.1 (fun s t h => by rw [hrepr s, hrepr t, h]) (by
      intro he
      have hp := Real.pi_pos
      rw [he, sub_self] at hdiff
      linarith)
  have hmono : StrictMono θ := hθ.1.strictMono_of_inj_boundedOrder (by
    change θ ⟨0, by norm_num⟩ ≤ θ ⟨1, by norm_num⟩
    linarith [Real.pi_pos]) hi
  exact ⟨θ, hmono, hdiff, hrepr⟩

/-- Any positively oriented simple parametrization of a circle has perimeter
at most the geometric circumference, even without differentiability. -/
theorem circle_perimeter_le_counterclockwise (γ : ℝ → Point) (c : Point) (r : ℝ)
    (hr : 0 < r)
    (hx : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (Metric.sphere c r) true (fun t : Icc (0 : ℝ) 1 => γ t)) :
    (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ≤ 2 * Real.pi * r := by
  let : Fact ((0 : ℝ) ≤ 1) := ⟨by norm_num⟩
  obtain ⟨θ, hmono, hdiff, hrepr⟩ := circle_monotone_angle _ c r hr hx
  have hθvar : eVariationOn θ univ = ENNReal.ofReal (2 * Real.pi) := by
    have hv := (hmono.monotone.monotoneOn univ).eVariationOn_eq
      (a := (⊥ : Icc (0 : ℝ) 1)) (b := ⊤) (mem_univ _) (mem_univ _)
    change θ (⊤ : Icc (0 : ℝ) 1) - θ ⊥ = 2 * Real.pi at hdiff
    simpa only [Icc_bot_top, inter_self, hdiff] using hv
  have hxvar : eVariationOn (fun t : Icc (0 : ℝ) 1 => γ t) univ =
      eVariationOn γ (Icc (0 : ℝ) 1) := by
    simpa only [Function.comp_def, image_univ, Subtype.range_coe_subtype, ofPred_mem_eq] using
      eVariationOn.comp_eq_of_monotoneOn γ (fun t : Icc (0 : ℝ) 1 => (t : ℝ))
        (t := univ) (fun _ _ _ _ h => h)
  have hv := (circle_map_lipschitz c r hr).lipschitzOnWith.comp_eVariationOn_le
    (g := θ) (s := univ) (fun _ _ => mem_univ _)
  have hfun : (fun t : Icc (0 : ℝ) 1 => γ t) =
      (fun a : ℝ => c + r • Complex.orthonormalBasisOneI.repr
        (Real.cos a + Real.sin a * Complex.I)) ∘ θ := funext hrepr
  rw [← hfun, hxvar, hθvar] at hv
  have hreal := ENNReal.toReal_mono (by finiteness) hv
  calc
    _ ≤ r * (2 * Real.pi) := by
      simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ hr.le,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi)] using hreal
    _ = 2 * Real.pi * r := by ring

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.simple_closed_lift_injective
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_monotone_angle
#check_upstream ClassicalTheorems.Progress.Isoperimetric.circle_perimeter_le_counterclockwise

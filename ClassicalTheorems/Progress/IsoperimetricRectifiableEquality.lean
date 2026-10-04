/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RectifiableExactParameter
import ClassicalTheorems.Progress.IsoperimetricACEquality

/-! Circle rigidity for arbitrary continuous rectifiable Jordan boundaries. -/

noncomputable section
open MeasureTheory Set MovingSofa Filter
namespace ClassicalTheorems.Progress.Isoperimetric

/-- Equality in the Lipschitz area bound forces a circle. -/
theorem jordan_lipschitz_equality_circle (δ : ℝ → Point) (K : NNReal)
    (hδ : LipschitzWith K δ) (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => δ t))
    (heq : 4 * Real.pi * ClassicalResults.area (jordanInterior Γ) = (K : ℝ) ^ 2) :
    ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r := by
  let T : Point ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let ζ := T ∘ δ
  have hζ : LipschitzWith K ζ := by simpa only [one_mul] using T.lipschitz.comp hδ
  have hclosed : δ 0 = δ 1 := horiented.2.2.2.2.1
  have hsimple : InjOn δ (Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hs := horiented.2.2.2.2.2.1 (x₁ := ⟨x, hx.1, hx.2.le⟩)
      (x₂ := ⟨y, hy.1, hy.2.le⟩) hx.2 hy.2 hxy
    exact congrArg Subtype.val hs
  have hζsimple : InjOn ζ (Ico (0 : ℝ) 1) := T.injective.comp_injOn hsimple
  have hζclosed : ζ 0 = ζ 1 := congrArg T hclosed
  have hacδ : AbsolutelyContinuousOnInterval δ 0 1 :=
    hδ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hcoordLip (i : Fin 2) := (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp hδ
  have hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => δ t i) 0 1 :=
    fun i => (hcoordLip i).lipschitzOnWith.absolutelyContinuousOnInterval
  have hdiff : ∀ᵐ t ∂volume, DifferentiableAt ℝ δ t := hδ.ae_differentiableAt
  have hdζ (t : ℝ) (ht : DifferentiableAt ℝ δ t) : deriv ζ t = T (deriv δ t) := by
    simpa only [ζ, Function.comp_def] using!
      (T.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv
  have hline : (∫ t in (0 : ℝ)..1, (ζ t).re * (deriv ζ t).im) =
      ∫ t in (0 : ℝ)..1, δ t 0 * deriv (fun s => δ s 1) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdiff] with t ht _
    rw [point_coordinate_deriv δ t ht 1, hdζ t ht]
    simp [ζ, T, Complex.mul_im, Complex.mul_re]
  have henergy : (∫ t in (0 : ℝ)..1,
      deriv (fun s => δ s 0) t ^ 2 + deriv (fun s => δ s 1) t ^ 2) =
      ∫ t in (0 : ℝ)..1, ‖deriv ζ t‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hdiff] with t ht _
    rw [point_coordinate_deriv δ t ht 0, point_coordinate_deriv δ t ht 1,
      hdζ t ht, T.norm_map, ← Point.norm_sq_eq]
  have harea := ac_signedArea_eq_jordanInterior_area δ hac Γ horiented
  have hlower := signed_area_le_energy_ac (fun t => δ t 0) (fun t => δ t 1)
    (hac 0) (hac 1) (congrArg (fun p : Point => p 0) hclosed)
    (congrArg (fun p : Point => p 1) hclosed)
    (lipschitz_deriv_memLp_two _ _ (hcoordLip 0))
    (lipschitz_deriv_memLp_two _ _ (hcoordLip 1))
  rw [harea, henergy] at hlower
  have hm : MemLp (deriv ζ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.of_bound (aestronglyMeasurable_deriv ζ _) K
      (Eventually.of_forall (fun _ => norm_deriv_le_of_lipschitz hζ))
  have hi : IntervalIntegrable (fun t => ‖deriv ζ t‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hupper : (∫ t in (0 : ℝ)..1, ‖deriv ζ t‖ ^ 2) ≤ (K : ℝ) ^ 2 := by
    calc
      _ ≤ ∫ _t in (0 : ℝ)..1, (K : ℝ) ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) hi intervalIntegrable_const
        intro t _
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_deriv_le_of_lipschitz hζ) 2
      _ = _ := by simp
  have he : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (ζ t).re * (deriv ζ t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv ζ t‖ ^ 2 := by
    rw [hline, harea]
    exact le_antisymm hlower (heq ▸ hupper)
  obtain ⟨c, r, hr, hcircle⟩ := area_energy_equality_circle_lipschitz ζ K hζ hζclosed hζsimple he
  have himage : T '' Γ = ζ '' Icc (0 : ℝ) 1 := by
    rw [← horiented.2.2.2.1]
    ext z
    constructor
    · rintro ⟨p, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨δ t, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
  refine ⟨T.symm c, r, hr, ?_⟩
  have hs := congrArg (fun S : Set ℂ => T.symm '' S) (himage.trans hcircle)
  simpa only [T.symm.image_sphere, image_image, T.symm_apply_apply, image_id'] using hs

/-- Every rectifiable Jordan curve attaining the sharp bound is exactly a
circle. Neither smoothness nor an a.e. speed condition is assumed. -/
theorem jordan_isoperimetric_equality_rectifiable (γ : ℝ → Point)
    (hBV : BoundedVariationOn γ (Icc (0 : ℝ) 1)) (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t))
    (heq : 4 * Real.pi * ClassicalResults.area (jordanInterior Γ) =
      (eVariationOn γ (Icc (0 : ℝ) 1)).toReal ^ 2) :
    ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r := by
  have hcont : ContinuousOn γ (Icc (0 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr horiented.2.2.1
  have hsimple : InjOn γ (Ico (0 : ℝ) 1) := by
    intro x hx y hy hxy
    have hs := horiented.2.2.2.2.2.1 (x₁ := ⟨x, hx.1, hx.2.le⟩)
      (x₂ := ⟨y, hy.1, hy.2.le⟩) hx.2 hy.2 hxy
    exact congrArg Subtype.val hs
  obtain ⟨δ, hδ, e, he⟩ := jordan_exact_lipschitz_parameter γ hcont hBV hsimple
  have hparam : (fun t : Icc (0 : ℝ) 1 => δ t) = (fun t : Icc (0 : ℝ) 1 => γ t) ∘ e := funext he
  have hOriented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => δ t) := by
    rw [hparam]
    exact oriented_jordan_comp_orderIso _ Γ horiented e
  apply jordan_lipschitz_equality_circle δ _ hδ Γ hOriented
  simpa only [Real.coe_toNNReal _ ENNReal.toReal_nonneg] using heq

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_lipschitz_equality_circle
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_equality_rectifiable

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricAC
import Mathlib.Analysis.Calculus.Rademacher

/-! Geometric Jordan area for absolutely continuous planar parametrizations.
The existing MovingSofa signed-area theorem is used as a dependency. -/

noncomputable section
open MeasureTheory Set MovingSofa Filter
open scoped Topology
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The derivative of an absolutely continuous representative is the density of
its interval Stieltjes measure, with no differentiability assumption at corners. -/
theorem ac_stieltjes_density (F : RightContinuousIntervalBV 0 1) (f : ℝ → ℝ)
    (hF : ∀ t : Icc (0 : ℝ) 1, F.toFun t = f t)
    (hf : AbsolutelyContinuousOnInterval f 0 1) :
    HasIntervalStieltjesDensity F (deriv f) := by
  have hext : ∀ t ∈ Icc (0 : ℝ) 1, stieltjesScalarExtension F t = f t := by
    intro t ht
    rw [stieltjesScalarExtension, dite_eq_left ht]
    exact hF ⟨t, ht⟩
  have hac : AbsolutelyContinuousOnInterval (stieltjesScalarExtension F) 0 1 :=
    hf.congr (fun t ht => (hext t (by simpa using ht)).symm)
  obtain ⟨ρ, hρ⟩ := (intervalStieltjes_absoluteContinuity 0 1 (by norm_num) F).1.1 hac
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      t ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ f t :=
    hf.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)
  have heq : ρ =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] deriv f := by
    filter_upwards [(intervalStieltjes_absoluteContinuity 0 1 (by norm_num) F).2 ρ hρ,
      hdiff, ae_restrict_mem measurableSet_Ioo] with t ht hd hmem
    have hm : t ∈ uIcc (0 : ℝ) 1 := by simpa using Ioo_subset_Icc_self hmem
    refine ht.unique ((hd hm).hasDerivAt.congr_of_eventuallyEq ?_)
    filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
    exact hext s (Ioo_subset_Icc_self hs)
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))] at heq
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    hf.intervalIntegrable_deriv, ?_⟩
  intro E hE
  rw [hρ.2 E hE]
  exact integral_congr_ae (heq.filter_mono (ae_mono Measure.restrict_le_self))

/-- An absolutely continuous planar path represented in the BV dependency. -/
def acBVPath (γ : ℝ → Point)
    (hcont : Continuous (fun t : Icc (0 : ℝ) 1 => γ t))
    (hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1) :
    ContinuousBVPaths 0 1 := by
  refine ⟨fun t => γ t, hcont, fun i => ?_⟩
  have hb : BoundedVariationOn (fun t => γ t i) (Icc (0 : ℝ) 1) := by
    simpa using (hac i).boundedVariationOn
  exact ne_top_of_le_ne_top hb
    (eVariationOn.comp_le_of_monotoneOn (fun t => γ t i)
      (Subtype.val : Icc (0 : ℝ) 1 → ℝ) (fun _ _ _ _ h => h) (fun t _ => t.property))

theorem acBVPath_coordinate_integral (γ : ℝ → Point)
    (hcont : Continuous (fun t : Icc (0 : ℝ) 1 => γ t))
    (hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1)
    (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate (acBVPath γ hcont hac) j)
      (fun t => (acBVPath γ hcont hac).val t i) univ =
      ∫ t in (0 : ℝ)..1, γ t i * deriv (fun s => γ s j) t := by
  have hd := ac_stieltjes_density (continuousBVCoordinate (acBVPath γ hcont hac) j)
    (fun t => γ t j) (fun _ => rfl) (hac j)
  have hc : Continuous (fun t : Icc (0 : ℝ) 1 => γ t i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hcont
  change intervalStieltjesIntegral (continuousBVCoordinate (acBVPath γ hcont hac) j)
    (fun t => γ t i) univ = _
  rw [intervalStieltjesIntegral_eq_integral_mul_of_density _ hd hc univ MeasurableSet.univ,
    setIntegral_univ]
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, γ t i * deriv (fun s => γ s j) t :=
      integral_subtype_comap measurableSet_Icc (fun t => γ t i * deriv (fun s => γ s j) t)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The signed line integral equals geometric Jordan area for absolutely
continuous coordinates and the dependency's topological positive orientation. -/
theorem ac_signedArea_eq_jordanInterior_area (γ : ℝ → Point)
    (hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1)
    (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) :
    (∫ t in (0 : ℝ)..1, γ t 0 * deriv (fun s => γ s 1) t) =
      ClassicalResults.area (jordanInterior Γ) := by
  have hcont : Continuous (fun t : Icc (0 : ℝ) 1 => γ t) := horiented.2.2.1
  have hc : γ 0 = γ 1 := horiented.2.2.2.2.1
  have harea := curveArea_eq_jordanInterior_area 0 1 (by norm_num) Γ
    (acBVPath γ hcont hac) horiented
  unfold curveAreaFunctional at harea
  rw [acBVPath_coordinate_integral, acBVPath_coordinate_integral] at harea
  have hibp := (hac 0).integral_mul_deriv_eq_deriv_mul (hac 1)
  rw [hc, sub_self, zero_sub] at hibp
  have hswap : (∫ t in (0 : ℝ)..1, deriv (fun s => γ s 0) t * γ t 1) =
      ∫ t in (0 : ℝ)..1, γ t 1 * deriv (fun s => γ s 0) t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hswap] at hibp
  linarith

/-- The sharp geometric area bound for an absolutely continuous oriented Jordan
boundary whose a.e. speed is bounded by L. This includes nonsmooth corners. -/
theorem jordan_area_le_speed_bound_ac (γ : ℝ → Point)
    (hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1)
    (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) (L : ℝ)
    (hspeed : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1),
      deriv (fun s => γ s 0) t ^ 2 + deriv (fun s => γ s 1) t ^ 2 ≤ L ^ 2) :
    4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤ L ^ 2 := by
  have hc : γ 0 = γ 1 := horiented.2.2.2.2.1
  rw [← ac_signedArea_eq_jordanInterior_area γ hac Γ horiented]
  exact signed_area_le_speed_bound_ac (fun t => γ t 0) (fun t => γ t 1)
    (hac 0) (hac 1) (congrArg (fun p : Point => p 0) hc)
    (congrArg (fun p : Point => p 1) hc) L hspeed


/-- Coordinate derivatives agree with the planar derivative wherever it exists. -/
theorem point_coordinate_deriv (γ : ℝ → Point) (t : ℝ)
    (hd : DifferentiableAt ℝ γ t) (i : Fin 2) :
    deriv (fun s => γ s i) t = deriv γ t i := by
  simpa [Function.comp_def, EuclideanSpace.proj] using! ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hd.hasDerivAt).deriv

/-- A Lipschitz Jordan parametrization bounds its geometric area by the square
of its Lipschitz constant. Corners and other exceptional points are allowed. -/
theorem jordan_area_le_lipschitz_bound (γ : ℝ → Point) (K : NNReal)
    (hLip : LipschitzWith K γ) (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) :
    4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤ (K : ℝ) ^ 2 := by
  have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1 :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval hacγ
  apply jordan_area_le_speed_bound_ac γ hac Γ horiented K
  have hd : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), DifferentiableAt ℝ γ t :=
    hLip.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)
  filter_upwards [hd] with t ht
  rw [point_coordinate_deriv γ t ht 0, point_coordinate_deriv γ t ht 1,
    ← Point.norm_sq_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_deriv_le_of_lipschitz hLip) 2

/-- The actual perimeter bound for a constant-speed Lipschitz Jordan boundary.
The speed condition is only a.e., so polygon corners do not violate it. -/
theorem jordan_isoperimetric_lipschitz_constant_speed (γ : ℝ → Point) (K : NNReal)
    (hLip : LipschitzWith K γ) (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) (L : ℝ)
    (hspeed : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), ‖deriv γ t‖ = L) :
    4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
  have hacγ : AbsolutelyContinuousOnInterval γ 0 1 :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hac : ∀ i : Fin 2, AbsolutelyContinuousOnInterval (fun t => γ t i) 0 1 :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval hacγ
  have hd : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), DifferentiableAt ℝ γ t :=
    hLip.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)
  have hb : 4 * Real.pi * ClassicalResults.area (jordanInterior Γ) ≤ L ^ 2 := by
    apply jordan_area_le_speed_bound_ac γ hac Γ horiented L
    filter_upwards [hd, hspeed] with t ht hs
    rw [point_coordinate_deriv γ t ht 0, point_coordinate_deriv γ t ht 1,
      ← Point.norm_sq_eq, hs]
  have hlength : (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) = L := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    calc
      _ = ∫ _t in Ioc (0 : ℝ) 1, L := integral_congr_ae hspeed
      _ = L := by simp
  rwa [hlength]

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ac_stieltjes_density
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ac_signedArea_eq_jordanInterior_area
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_area_le_speed_bound_ac
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_area_le_lipschitz_bound
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_lipschitz_constant_speed

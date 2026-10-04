/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.Green
import MovingSofa.Curve.Jordan.SignedArea
import MovingSofa.Analysis.Stieltjes.Smooth
import MovingSofa.Analysis.Stieltjes.DensityIntegration

/-! Verified results for the area step of Green’s theorem. The full arbitrary-field identity
is proved in `ClassicalTheorems.Progress.GreenFull`. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Green

private theorem coordinate_contDiff (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ) (i : Fin 2) :
    ContDiff ℝ 1 (fun t => γ t i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hγ

/-- A C¹ planar curve, restricted to [0,1], is a continuous BV path. -/
def c1BVPath (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ) : ContinuousBVPaths 0 1 := by
  refine ⟨fun t => γ t, hγ.continuous.comp continuous_subtype_val, fun i => ?_⟩
  obtain ⟨F, hF, _⟩ := exists_intervalBV_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (by norm_num) (fun t => γ t i) (deriv (fun t => γ t i))
    (fun t => ((coordinate_contDiff γ hγ i).differentiable one_ne_zero t).hasDerivAt)
    (coordinate_contDiff γ hγ i).continuous_deriv_one
  have heq : F.toFun = (fun t : Icc (0 : ℝ) 1 => γ t i) := funext hF
  rw [← heq]
  exact F.boundedVariation

theorem c1BVPath_coordinate_density (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ) (i : Fin 2) :
    HasIntervalStieltjesDensity (continuousBVCoordinate (c1BVPath γ hγ) i)
      (deriv (fun t => γ t i)) := by
  obtain ⟨F, hF, hd⟩ := exists_intervalBV_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (by norm_num) (fun t => γ t i) (deriv (fun t => γ t i))
    (fun t => ((coordinate_contDiff γ hγ i).differentiable one_ne_zero t).hasDerivAt)
    (coordinate_contDiff γ hγ i).continuous_deriv_one
  have heq : F = continuousBVCoordinate (c1BVPath γ hγ) i :=
    RightContinuousIntervalBV.toFun_injective (funext hF)
  rwa [heq] at hd

/-- A continuous integrand against a C¹ coordinate's Stieltjes measure is the
ordinary line integral with that coordinate derivative. -/
theorem c1BVPath_stieltjes_integral (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (j : Fin 2) (q : ℝ → ℝ) (hq : ContinuousOn q (Icc 0 1)) :
    intervalStieltjesIntegral (continuousBVCoordinate (c1BVPath γ hγ) j)
      (fun t => q t) univ =
      ∫ t in (0 : ℝ)..1, q t * deriv (fun s => γ s j) t := by
  have hq' : Continuous (fun t : Icc (0 : ℝ) 1 => q t) := hq.domRestrict
  rw [intervalStieltjesIntegral_eq_integral_mul_of_density _
    (c1BVPath_coordinate_density γ hγ j) hq' univ MeasurableSet.univ,
    setIntegral_univ]
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, q t * deriv (fun s => γ s j) t :=
      integral_subtype_comap measurableSet_Icc
        (fun t => q t * deriv (fun s => γ s j) t)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem c1BVPath_coordinate_integral (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (i j : Fin 2) :
    intervalStieltjesIntegral (continuousBVCoordinate (c1BVPath γ hγ) j)
      (fun t => (c1BVPath γ hγ).val t i) univ =
      ∫ t in (0 : ℝ)..1, γ t i * deriv (fun s => γ s j) t := by
  exact c1BVPath_stieltjes_integral γ hγ j (fun t => γ t i)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hγ.continuous).continuousOn

/-- The Stieltjes area functional equals the ordinary C¹ signed-area integral. -/
theorem c1BVPath_signedArea (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) :
    curveAreaFunctional (c1BVPath γ hγ) = signedArea (fun t => γ t 0) (fun t => γ t 1) := by
  unfold curveAreaFunctional
  rw [c1BVPath_coordinate_integral, c1BVPath_coordinate_integral]
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1)
    (fun t _ => ((coordinate_contDiff γ hγ 0).differentiable one_ne_zero t).hasDerivAt)
    (fun t _ => ((coordinate_contDiff γ hγ 1).differentiable one_ne_zero t).hasDerivAt)
    ((coordinate_contDiff γ hγ 0).continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
    ((coordinate_contDiff γ hγ 1).continuous_deriv_one.intervalIntegrable (μ := volume) 0 1)
  have hc : (∫ t in (0 : ℝ)..1, deriv (fun s => γ s 0) t * γ t 1) =
      ∫ t in (0 : ℝ)..1, γ t 1 * deriv (fun s => γ s 0) t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact mul_comm _ _
  rw [hc, hclosed, sub_self, zero_sub] at hb
  unfold signedArea
  linarith

/-- The Jordan signed-area identity for a globally C¹ curve, with upstream
orientation expressed explicitly by its angle-lift winding definition. -/
theorem c1_signedArea_eq_jordanInterior_area (γ : ℝ → Point) (hγ : ContDiff ℝ 1 γ)
    (Γ : Set Point)
    (horiented : IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1) Γ true
      (fun t : Icc (0 : ℝ) 1 => γ t)) :
    signedArea (fun t => γ t 0) (fun t => γ t 1) =
      ClassicalResults.area (jordanInterior Γ) := by
  have hc : γ 0 = γ 1 := horiented.2.2.2.2.1
  rw [← c1BVPath_signedArea γ hγ hc]
  exact curveArea_eq_jordanInterior_area 0 1 (by norm_num) Γ (c1BVPath γ hγ) horiented

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.c1BVPath_coordinate_density
#check_upstream ClassicalTheorems.Progress.Green.c1BVPath_coordinate_integral
#check_upstream ClassicalTheorems.Progress.Green.c1BVPath_signedArea
#check_upstream ClassicalTheorems.Progress.Green.c1_signedArea_eq_jordanInterior_area

#check_upstream ClassicalTheorems.Progress.Green.c1BVPath_stieltjes_integral

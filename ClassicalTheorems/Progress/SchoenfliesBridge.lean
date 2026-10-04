/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.PeriodicWinding
import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Connecting the licensed Schönflies dependency to our interval Jordan curves. -/

noncomputable section
open Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A simple closed unit-interval parametrization satisfies the dependency's loop definition. -/
theorem schoenflies_jordan_of_unit_param (x : Icc (0 : ℝ) 1 → Point)
    (hx : Continuous x) (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) : Schoenflies.IsJordanCurve (range x) := by
  let f : ℝ → Point := fun t => if ht : t ∈ Icc (0 : ℝ) 1 then x ⟨t, ht⟩
    else x ⟨0, by norm_num⟩
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t = x ⟨t, ht⟩ := by
    dsimp only [f]
    exact dite_eq_left ht
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hx using 1
    funext t
    exact hf t t.property
  · simpa only [hf 0 (by norm_num), hf 1 (by norm_num)] using hclosed
  · intro s hs t ht he
    have h := hinj (x₁ := ⟨s, hs.1, hs.2.le⟩) (x₂ := ⟨t, ht.1, ht.2.le⟩)
      hs.2 ht.2 (by
        rw [hf s ⟨hs.1, hs.2.le⟩, hf t ⟨ht.1, ht.2.le⟩] at he
        exact he)
    exact congrArg Subtype.val h
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (hf t ht).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, hf t t.property⟩

/-- The dependency recognizes the usual Euclidean unit circle as a Jordan curve. -/
theorem schoenflies_jordan_unit_circle :
    Schoenflies.IsJordanCurve (Metric.sphere (0 : Point) 1) := by
  let T : ℂ ≃ₗᵢ[ℝ] Point := Complex.orthonormalBasisOneI.repr
  let f : ℝ → Point := fun t => T (Circle.exp (2 * Real.pi * t - Real.pi) : ℂ)
  have hf : Continuous f := T.continuous.comp
    (continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop)))
  refine ⟨f, ⟨hf.continuousOn, ?_, ?_⟩, ?_⟩
  · change T (Circle.exp (2 * Real.pi * 0 - Real.pi) : ℂ) =
      T (Circle.exp (2 * Real.pi * 1 - Real.pi) : ℂ)
    apply congrArg T
    apply congrArg (fun z : Circle => (z : ℂ))
    apply Circle.exp_eq_exp.mpr
    exact ⟨-1, by norm_num; ring⟩
  · intro s hs t ht he
    rcases hs with ⟨hs0, hs1⟩
    rcases ht with ⟨ht0, ht1⟩
    have hst : Circle.exp (2 * Real.pi * s - Real.pi) =
        Circle.exp (2 * Real.pi * t - Real.pi) :=
      Circle.coe_injective (T.injective he)
    have h := Circle.exp_injOn_Ico
      (a := -Real.pi) (b := Real.pi) (by linarith)
      (x₁ := 2 * Real.pi * s - Real.pi)
      (x₂ := 2 * Real.pi * t - Real.pi)
      (by constructor <;> nlinarith [Real.pi_pos])
      (by constructor <;> nlinarith [Real.pi_pos]) hst
    nlinarith [Real.pi_pos]
  · ext z
    constructor
    · rintro ⟨t, -, rfl⟩
      rw [mem_sphere_zero_iff_norm, T.norm_map]
      exact Circle.norm_coe _
    · intro hz
      let c : Circle := ⟨T.symm z, mem_sphere_zero_iff_norm.mpr (by
        rw [T.symm.norm_map]
        exact mem_sphere_zero_iff_norm.mp hz)⟩
      obtain ⟨r, hr, he⟩ := Circle.surjOn_exp_neg_pi_pi (mem_univ c)
      let t := (r + Real.pi) / (2 * Real.pi)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [hr.1]) (by positivity)
        · exact (div_le_one (by positivity)).mpr (by linarith [hr.2])
      refine ⟨t, ht, ?_⟩
      have ht' : 2 * Real.pi * t - Real.pi = r := by
        dsimp [t]
        field_simp
        ring
      change T (Circle.exp (2 * Real.pi * t - Real.pi) : ℂ) = z
      rw [ht', he]
      exact T.apply_symm_apply z

/-- Every simple closed interval loop is the image of the circle under a plane homeomorphism. -/
theorem exists_circle_ambient_homeomorph (x : Icc (0 : ℝ) 1 → Point)
    (hx : Continuous x) (hclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩)
    (hinj : InjOn x {t | (t : ℝ) < 1}) :
    ∃ e : Point ≃ₜ Point, e '' Metric.sphere (0 : Point) 1 = range x := by
  have hΓ := schoenflies_jordan_of_unit_param x hx hclosed hinj
  obtain ⟨h⟩ := schoenflies_jordan_unit_circle.homeomorph hΓ
  obtain ⟨e, he⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    schoenflies_jordan_unit_circle hΓ h
  refine ⟨e, ?_⟩
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [he ⟨w, hw⟩]
    exact (h ⟨w, hw⟩).property
  · intro hz
    let w := h.symm ⟨z, hz⟩
    refine ⟨w, w.property, ?_⟩
    rw [he w]
    exact congrArg Subtype.val (h.apply_symm_apply ⟨z, hz⟩)

end ClassicalTheorems.Progress.Isoperimetric

#check_upstream Schoenflies.jordan_schoenflies_of_homeomorph
#check_upstream ClassicalTheorems.Progress.Isoperimetric.schoenflies_jordan_of_unit_param
#check_upstream ClassicalTheorems.Progress.Isoperimetric.schoenflies_jordan_unit_circle
#check_upstream ClassicalTheorems.Progress.Isoperimetric.exists_circle_ambient_homeomorph

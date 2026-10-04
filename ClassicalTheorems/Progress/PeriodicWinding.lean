/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.LoopCircleDeformation
import Mathlib.Analysis.Convex.Contractible

/-! Winding under an arbitrary integer traversal of a periodic planar loop. -/

noncomputable section
open Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- A continuous path on the whole real line avoiding a point has a global angle lift. -/
theorem exists_global_angle_lift (f : ℝ → Point) (p : Point)
    (hf : Continuous f) (hp : p ∉ range f) :
    ∃ α : ℝ → ℝ, Continuous α ∧ ∀ t,
      Real.cos (α t) = (f t - p) 0 / ‖f t - p‖ ∧
      Real.sin (α t) = (f t - p) 1 / ‖f t - p‖ := by
  let z : ℝ → ℂ := fun t => Complex.orthonormalBasisOneI.repr.symm (f t - p)
  have hz : Continuous z :=
    Complex.orthonormalBasisOneI.repr.symm.continuous.comp (hf.sub continuous_const)
  have hn (t : ℝ) : z t ≠ 0 := by
    rw [← norm_ne_zero_iff, Complex.orthonormalBasisOneI.repr.symm.norm_map,
      norm_ne_zero_iff, sub_ne_zero]
    exact fun h => hp ⟨t, h⟩
  let ϑ : ℝ → Real.Angle := fun t => (Complex.arg (z t) : Real.Angle)
  have hϑ : Continuous ϑ := by
    rw [continuous_iff_continuousAt]
    exact fun t => (Complex.continuousAt_arg_coe_angle (hn t)).comp hz.continuousAt
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) :=
    AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, -⟩ := hcov.existsUnique_continuousMap_lifts
    (⟨ϑ, hϑ⟩ : C(ℝ, Real.Angle)) 0 (Complex.arg (z 0)) rfl
  refine ⟨α, α.continuous, fun t => ?_⟩
  have he : (α t : Real.Angle) = (Complex.arg (z t) : Real.Angle) :=
    congrFun hα.2 t
  constructor
  · have h := congrArg Real.Angle.cos he
    rw [Real.Angle.cos_coe, Real.Angle.cos_coe, Complex.cos_arg (hn t)] at h
    change _ = (Complex.orthonormalBasisOneI.repr.symm (f t - p)).re /
      ‖Complex.orthonormalBasisOneI.repr.symm (f t - p)‖ at h
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map] at h
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply] using h
  · have h := congrArg Real.Angle.sin he
    rw [Real.Angle.sin_coe, Real.Angle.sin_coe, Complex.sin_arg] at h
    change _ = (Complex.orthonormalBasisOneI.repr.symm (f t - p)).im /
      ‖Complex.orthonormalBasisOneI.repr.symm (f t - p)‖ at h
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map] at h
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply] using h

/-- A lift of a periodic loop has the same increment at every integer translate. -/
theorem periodic_angle_increment (f : ℝ → Point) (p : Point) (α : ℝ → ℝ)
    (hα : Continuous α) (hlift : ∀ t,
      Real.cos (α t) = (f t - p) 0 / ‖f t - p‖ ∧
      Real.sin (α t) = (f t - p) 1 / ‖f t - p‖)
    (hperiod : Function.Periodic f 1) (t : ℝ) (n : ℤ) :
    α (t + n) - α t = (n : ℝ) * (α 1 - α 0) := by
  have hstep (s : ℝ) : α (s + 1) - α s = α 1 - α 0 := by
    have hshift : Continuous (fun s : ℝ => α (s + 1)) :=
      hα.comp (continuous_id.add continuous_const)
    have h := Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin
      hshift hα
      (fun s => by rw [(hlift _).1, (hlift _).1, hperiod s])
      (fun s => by rw [(hlift _).2, (hlift _).2, hperiod s]) s 0
    simpa using h
  let β : ℝ → ℝ := fun s => α s - s * (α 1 - α 0)
  have hβ : Function.Periodic β 1 := by
    intro s
    dsimp [β]
    linarith [hstep s]
  have h := hβ.int_mul n t
  simp only [mul_one] at h
  dsimp [β] at h
  nlinarith

/-- Traversing a continuous period-one loop `n` times multiplies its integral winding by `n`.
The interval and phase are arbitrary, and negative traversals are included. -/
theorem winding_periodic_integer_traversal {a b : ℝ} (hab : a < b)
    (f : ℝ → Point) (p : Point) (hf : Continuous f) (hp : p ∉ range f)
    (hperiod : Function.Periodic f 1) (phase : ℝ) (n : ℤ) :
    ∃ m : ℤ,
      curveWinding (by norm_num : (0 : ℝ) ≤ 1)
        (fun t : Icc (0 : ℝ) 1 => f (phase + t)) p = (m : ℝ) ∧
      curveWinding hab.le
        (fun t : Icc a b => f (phase + (n : ℝ) * (((t : ℝ) - a) / (b - a)))) p =
          (n : ℝ) * (m : ℝ) := by
  obtain ⟨α, hα, hlift⟩ := exists_global_angle_lift f p hf hp
  let θ : Icc (0 : ℝ) 1 → ℝ := fun t => α (phase + t)
  have hθ : IsCurveAngleLift (fun t : Icc (0 : ℝ) 1 => f (phase + t)) p θ :=
    ⟨hα.comp (continuous_const.add continuous_subtype_val), fun t => hlift _⟩
  have hclosed : f (phase + (0 : ℝ)) = f (phase + 1) := by
    simpa using (hperiod phase).symm
  obtain ⟨m, hm, hw⟩ := angleLift_integer_increment (by norm_num) _ p θ hθ hclosed
  have hm' : α 1 - α 0 = (m : ℝ) * (2 * Real.pi) := by
    have h := periodic_angle_increment f p α hα hlift hperiod phase 1
    norm_num at h
    simp only [θ, add_zero] at hm
    exact h.symm.trans hm
  let ψ : Icc a b → ℝ := fun t => α (phase + (n : ℝ) * (((t : ℝ) - a) / (b - a)))
  have hψ : IsCurveAngleLift
      (fun t : Icc a b => f (phase + (n : ℝ) * (((t : ℝ) - a) / (b - a)))) p ψ := by
    refine ⟨hα.comp ?_, fun t => hlift _⟩
    fun_prop
  refine ⟨m, hw, ?_⟩
  rw [hψ.curveWinding_eq]
  simp only [ψ, sub_self, zero_div, mul_zero, add_zero,
    div_self (sub_ne_zero.mpr hab.ne'), mul_one]
  rw [periodic_angle_increment f p α hα hlift hperiod phase n, hm']
  field_simp

end ClassicalTheorems.Progress.Isoperimetric

#check_upstream ClassicalTheorems.Progress.Isoperimetric.exists_global_angle_lift
#check_upstream ClassicalTheorems.Progress.Isoperimetric.periodic_angle_increment
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_periodic_integer_traversal

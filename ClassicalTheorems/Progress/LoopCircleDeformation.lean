/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.WindingPerturbation

/-! Constructing an integer-circle normal form for every closed planar loop
avoiding a basepoint. The Jordan-specific primitive-degree step remains separate. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- The unit vector with the given angle. -/
def angularPoint (θ : ℝ) : Point :=
  Complex.orthonormalBasisOneI.repr (Real.cos θ + Real.sin θ * Complex.I)

theorem continuous_angularPoint : Continuous angularPoint := by
  have h : Continuous (fun θ : ℝ => (Real.cos θ : ℂ) + Real.sin θ * Complex.I) := by
    fun_prop
  exact Complex.orthonormalBasisOneI.repr.continuous.comp h

theorem norm_angularPoint (θ : ℝ) : ‖angularPoint θ‖ = 1 := by
  rw [angularPoint, Complex.orthonormalBasisOneI.repr.norm_map,
    Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.norm_cos_add_sin_mul_I θ

/-- An angle lift reconstructs the original loop with its actual radial distance. -/
theorem angleLift_radial_representation {a b : ℝ} (x : Icc a b → Point) (p : Point)
    (θ : Icc a b → ℝ) (hθ : IsCurveAngleLift x p θ) (hp : p ∉ range x)
    (t : Icc a b) : x t = p + ‖x t - p‖ • angularPoint (θ t) := by
  have hn : ‖x t - p‖ ≠ 0 := norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (fun he => hp ⟨t, he⟩))
  have he0 := (eq_div_iff hn).mp (hθ.2 t).1
  have he1 := (eq_div_iff hn).mp (hθ.2 t).2
  ext i
  fin_cases i <;>
    simp [angularPoint, Complex.orthonormalBasisOneI_repr_apply,
      Complex.mul_re, Complex.mul_im]
  · change x t 0 = p 0 + ‖x t - p‖ * Real.cos (θ t)
    change Real.cos (θ t) * ‖x t - p‖ = x t 0 - p 0 at he0
    nlinarith
  · change x t 1 = p 1 + ‖x t - p‖ * Real.sin (θ t)
    change Real.sin (θ t) * ‖x t - p‖ = x t 1 - p 1 at he1
    nlinarith

/-- Closedness makes every angle increment an integer number of full turns. -/
theorem angleLift_integer_increment {a b : ℝ} (hab : a ≤ b)
    (x : Icc a b → Point) (p : Point) (θ : Icc a b → ℝ)
    (hθ : IsCurveAngleLift x p θ)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩) :
    ∃ n : ℤ, θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩ = (n : ℝ) * (2 * Real.pi) ∧
      curveWinding hab x p = (n : ℝ) := by
  have hcos : Real.cos (θ ⟨b, hab, le_rfl⟩) = Real.cos (θ ⟨a, le_rfl, hab⟩) := by
    rw [(hθ.2 _).1, (hθ.2 _).1, hclosed]
  have hsin : Real.sin (θ ⟨b, hab, le_rfl⟩) = Real.sin (θ ⟨a, le_rfl, hab⟩) := by
    rw [(hθ.2 _).2, (hθ.2 _).2, hclosed]
  have hc : Real.cos (θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩) = 1 := by
    rw [Real.cos_sub, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (θ ⟨a, le_rfl, hab⟩)]
  obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hc
  refine ⟨n, hn.symm, ?_⟩
  rw [hθ.curveWinding_eq, ← hn]
  field_simp

/-- A concrete deformation from a loop to a unit circle traversed `degree` times.
It is a certificate constructed below, rather than an additional loop hypothesis. -/
structure IntegerCircleDeformation {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) where
  degree : ℤ
  phase : ℝ
  winding_eq : curveWinding hab.le x p = (degree : ℝ)
  H : Icc (0 : ℝ) 1 → Icc a b → Point
  continuous : Continuous (Function.uncurry H)
  closed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩
  avoids : ∀ u, p ∉ range (H u)
  start : H ⟨0, by norm_num⟩ = x
  finish : H ⟨1, by norm_num⟩ = fun t : Icc a b =>
    p + angularPoint (phase + (degree : ℝ) * (2 * Real.pi) * (((t : ℝ) - a) / (b - a)))

/-- Every continuous closed loop avoiding a point admits an explicit deformation
to an integer traversal of the unit circle around that point. -/
theorem nonempty_integer_circle_deformation {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) (hx : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩) :
    Nonempty (IntegerCircleDeformation hab x p) := by
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab hx hp
  obtain ⟨n, hn, hw⟩ := angleLift_integer_increment hab.le x p θ hθ hclosed
  let A : Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Icc a b := ⟨b, hab.le, le_rfl⟩
  let clock : Icc a b → ℝ := fun t => ((t : ℝ) - a) / (b - a)
  let κ : Icc a b → ℝ := fun t => θ A + (θ B - θ A) * clock t
  let ρ : Icc (0 : ℝ) 1 → Icc a b → ℝ :=
    fun u t => (1 - (u : ℝ)) * ‖x t - p‖ + (u : ℝ)
  let α : Icc (0 : ℝ) 1 → Icc a b → ℝ :=
    fun u t => (1 - (u : ℝ)) * θ t + (u : ℝ) * κ t
  let H : Icc (0 : ℝ) 1 → Icc a b → Point :=
    fun u t => p + ρ u t • angularPoint (α u t)
  have hclock : Continuous clock := (continuous_subtype_val.sub continuous_const).div_const _
  have hκ : Continuous κ := continuous_const.add (continuous_const.mul hclock)
  have hρ : Continuous (Function.uncurry ρ) := by
    dsimp [ρ, Function.uncurry]
    fun_prop
  have hα : Continuous (Function.uncurry α) := by
    have hθcont : Continuous θ := hθ.1
    dsimp [α, Function.uncurry]
    fun_prop
  have hH : Continuous (Function.uncurry H) :=
    continuous_const.add (hρ.smul (continuous_angularPoint.comp hα))
  have hρpos (u : Icc (0 : ℝ) 1) (t : Icc a b) : 0 < ρ u t := by
    have ht : 0 < ‖x t - p‖ := norm_pos_iff.mpr
      (sub_ne_zero.mpr (fun he => hp ⟨t, he⟩))
    by_cases hu : (u : ℝ) = 1
    · simp [ρ, hu]
    · have hlt : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 hu
      exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) ht) u.property.1
  have hκa : κ A = θ A := by simp [κ, clock, A]
  have hclockb : clock B = 1 := by
    dsimp [clock, B]
    exact div_self (sub_ne_zero.mpr hab.ne')
  have hκb : κ B = θ B := by dsimp [κ]; rw [hclockb]; ring
  have hαa (u : Icc (0 : ℝ) 1) : α u A = θ A := by dsimp [α]; rw [hκa]; ring
  have hαb (u : Icc (0 : ℝ) 1) : α u B = θ B := by dsimp [α]; rw [hκb]; ring
  have hρend (u : Icc (0 : ℝ) 1) : ρ u A = ρ u B := by
    simp only [ρ, A, B, hclosed]
  have hqend : angularPoint (θ A) = angularPoint (θ B) := by
    have hcos : Real.cos (θ A) = Real.cos (θ B) := by
      rw [(hθ.2 A).1, (hθ.2 B).1]
      simp only [A, B, hclosed]
    have hsin : Real.sin (θ A) = Real.sin (θ B) := by
      rw [(hθ.2 A).2, (hθ.2 B).2]
      simp only [A, B, hclosed]
    simp only [angularPoint, hcos, hsin]
  have hHclosed (u : Icc (0 : ℝ) 1) : H u A = H u B := by
    dsimp [H]
    rw [hαa, hαb, hρend, hqend]
  have hHavoid (u : Icc (0 : ℝ) 1) : p ∉ range (H u) := by
    rintro ⟨t, ht⟩
    have hnorm : ‖H u t - p‖ = ρ u t := by
      simp [H, norm_smul, norm_angularPoint, abs_of_pos (hρpos u t)]
    rw [ht, sub_self, norm_zero] at hnorm
    exact (hρpos u t).ne' hnorm.symm
  refine ⟨{
    degree := n
    phase := θ A
    winding_eq := hw
    H := H
    continuous := hH
    closed := hHclosed
    avoids := hHavoid
    start := ?_
    finish := ?_ }⟩
  · funext t
    simpa [H, ρ, α] using (angleLift_radial_representation x p θ hθ hp t).symm
  · funext t
    dsimp [H, ρ, α, κ, clock]
    simp only [sub_self, zero_mul, zero_add, one_mul, one_smul]
    change θ B - θ A = (n : ℝ) * (2 * Real.pi) at hn
    rw [hn]

/-- A contraction through closed loops in the plane with `p` removed. -/
structure PuncturedLoopContraction {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) where
  point : Point
  point_ne : point ≠ p
  H : Icc (0 : ℝ) 1 → Icc a b → Point
  continuous : Continuous (Function.uncurry H)
  closed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩
  avoids : ∀ u, p ∉ range (H u)
  start : H ⟨0, by norm_num⟩ = x
  finish : H ⟨1, by norm_num⟩ = fun _ => point

/-- A closed loop contracts without passing through the basepoint exactly when
its winding vanishes. No simplicity assumption is required. -/
theorem winding_zero_iff_contractible {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) (hx : Continuous x) (hp : p ∉ range x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩) :
    curveWinding hab.le x p = 0 ↔ Nonempty (PuncturedLoopContraction hab x p) := by
  constructor
  · intro hw
    obtain ⟨D⟩ := nonempty_integer_circle_deformation hab x p hx hp hclosed
    have hn : D.degree = 0 := by
      have he : (D.degree : ℝ) = 0 := D.winding_eq.symm.trans hw
      exact Int.cast_eq_zero.mp he
    refine ⟨{
      point := p + angularPoint D.phase
      point_ne := ?_
      H := D.H
      continuous := D.continuous
      closed := D.closed
      avoids := D.avoids
      start := D.start
      finish := ?_ }⟩
    · intro he
      have hq : angularPoint D.phase = 0 := add_left_cancel (he.trans (add_zero p).symm)
      have := norm_angularPoint D.phase
      rw [hq, norm_zero] at this
      norm_num at this
    · simpa only [hn, Int.cast_zero, zero_mul, add_zero] using D.finish
  · rintro ⟨D⟩
    have he := winding_eq_of_continuous_deformation hab D.H p
      D.continuous D.closed D.avoids
    rw [D.start, D.finish] at he
    have hv : D.point - p ≠ 0 := sub_ne_zero.mpr D.point_ne
    have hz : curveWinding hab.le (fun _ : Icc a b => D.point) p = 0 :=
      curveWinding_eq_zero_of_inner_pos hab.le continuous_const rfl p (D.point - p)
        hv (fun _ => real_inner_self_pos.mpr hv)
    exact he.symm.trans hz

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angularPoint
#check_upstream ClassicalTheorems.Progress.Isoperimetric.continuous_angularPoint
#check_upstream ClassicalTheorems.Progress.Isoperimetric.norm_angularPoint
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angleLift_radial_representation
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angleLift_integer_increment
#check_upstream ClassicalTheorems.Progress.Isoperimetric.nonempty_integer_circle_deformation
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_zero_iff_contractible

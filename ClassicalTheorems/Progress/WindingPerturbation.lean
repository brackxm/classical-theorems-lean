/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RadialWinding
import Mathlib.Topology.ContinuousMap.Compact

/-! Winding survives small changes of a closed loop. This transfers geometric
orientation certificates to boundaries that need not be radially unique. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

private theorem complex_relative_dot (v w : Point) :
    (starRingEnd ℂ (Complex.orthonormalBasisOneI.repr.symm v) *
      Complex.orthonormalBasisOneI.repr.symm w).re = inner ℝ v w := by
  rw [mul_comm, ← Complex.inner, Complex.orthonormalBasisOneI.repr.symm.inner_map_map]

/-- Changing a radial vector by less than its length preserves a positive dot product. -/
theorem inner_pos_of_small_displacement (x y p : Point)
    (h : ‖y - x‖ < ‖x - p‖) : 0 < inner ℝ (x - p) (y - p) := by
  have hn : 0 < ‖x - p‖ := lt_of_le_of_lt (norm_nonneg _) h
  have he : y - p = (x - p) + (y - x) := by abel
  rw [he, inner_add_right, real_inner_self_eq_norm_sq]
  have hl := neg_le_of_abs_le (abs_real_inner_le_norm (x - p) (y - x))
  nlinarith

/-- Two continuous closed loops with positively aligned radial vectors have
the same winding. Neither loop needs differentiability, rectifiability or simplicity. -/
theorem winding_eq_of_inner_pos {a b : ℝ} (hab : a < b)
    (x y : Icc a b → Point) (p : Point) (hx : Continuous x) (hy : Continuous y)
    (hxc : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    (hpos : ∀ t, 0 < inner ℝ (x t - p) (y t - p)) :
    curveWinding hab.le y p = curveWinding hab.le x p := by
  let T : ℂ ≃ₗᵢ[ℝ] Point := Complex.orthonormalBasisOneI.repr
  let z : Icc a b → ℂ := fun t => T.symm (x t - p)
  let w : Icc a b → ℂ := fun t => T.symm (y t - p)
  have hz : Continuous z := T.symm.continuous.comp (hx.sub continuous_const)
  have hw : Continuous w := T.symm.continuous.comp (hy.sub continuous_const)
  have hd (t : Icc a b) : 0 < (starRingEnd ℂ (z t) * w t).re := by
    simpa only [z, w, T, complex_relative_dot] using hpos t
  have hzn (t : Icc a b) : z t ≠ 0 := by
    intro h
    have hh := hd t
    simp [h] at hh
  have hwn (t : Icc a b) : w t ≠ 0 := by
    intro h
    have hh := hd t
    simp [h] at hh
  have havoid : p ∉ range x := by
    rintro ⟨t, ht⟩
    apply hzn t
    simp [z, ht]
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab hx havoid
  let δ : Icc a b → ℝ := fun t => Complex.arg (starRingEnd ℂ (z t) * w t)
  have hδ : Continuous δ := continuous_arg_conj_mul_of_re_pos hz hw hd
  have hη : IsCurveAngleLift y p (fun t => θ t + δ t) := by
    refine ⟨hθ.1.add hδ, fun t => ?_⟩
    have hcθ : Real.cos (θ t) = (z t).re / ‖z t‖ := by
      rw [show ‖z t‖ = ‖x t - p‖ from T.symm.norm_map _]
      simpa [z, T, Complex.orthonormalBasisOneI_repr_symm_apply] using (hθ.2 t).1
    have hsθ : Real.sin (θ t) = (z t).im / ‖z t‖ := by
      rw [show ‖z t‖ = ‖x t - p‖ from T.symm.norm_map _]
      simpa [z, T, Complex.orthonormalBasisOneI_repr_symm_apply] using (hθ.2 t).2
    have hrot := normalized_complex_rotation_by_relative_arg (hzn t) (hwn t) hcθ hsθ
    rw [show ‖w t‖ = ‖y t - p‖ from T.symm.norm_map _] at hrot
    simpa [δ, w, T, Complex.orthonormalBasisOneI_repr_symm_apply] using hrot
  have hδend : δ ⟨a, le_rfl, hab.le⟩ = δ ⟨b, hab.le, le_rfl⟩ := by
    simp only [δ, z, w, hxc, hyc]
  rw [hη.curveWinding_eq, hθ.curveWinding_eq]
  simp only [hδend]
  ring

/-- A pointwise perturbation smaller than the radial distance preserves winding. -/
theorem winding_eq_of_small_displacement {a b : ℝ} (hab : a < b)
    (x y : Icc a b → Point) (p : Point) (hx : Continuous x) (hy : Continuous y)
    (hxc : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    (hnear : ∀ t, ‖y t - x t‖ < ‖x t - p‖) :
    curveWinding hab.le y p = curveWinding hab.le x p :=
  winding_eq_of_inner_pos hab x y p hx hy hxc hyc
    (fun t => inner_pos_of_small_displacement (x t) (y t) p (hnear t))

/-- Every continuous closed loop avoiding a point has a positive uniform
perturbation radius within which all continuous closed loops have the same winding. -/
theorem exists_winding_stability_radius {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (p : Point) (hx : Continuous x) (hp : p ∉ range x)
    (hxc : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Icc a b → Point, Continuous y →
      y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩ →
      (∀ t, ‖y t - x t‖ < ε) → curveWinding hab.le y p = curveWinding hab.le x p := by
  let : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  obtain ⟨t₀, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty
    (hx.sub continuous_const).norm.continuousOn
  have hε : 0 < ‖x t₀ - p‖ := norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun he => hp ⟨t₀, he⟩))
  refine ⟨‖x t₀ - p‖, hε, fun y hy hyc hnear => ?_⟩
  exact winding_eq_of_small_displacement hab x y p hx hy hxc hyc
    (fun t => (hnear t).trans_le (hmin (mem_univ t)))

/-- Nonzero winding forces an off-boundary point into the geometric Jordan interior. -/
theorem mem_jordanInterior_of_winding_ne_zero {a b : ℝ} (hab : a ≤ b)
    (x : Icc a b → Point) (Γ : Set Point) (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (p : Point) (hw : curveWinding hab x p ≠ 0) : p ∈ jordanInterior Γ := by
  have hp : p ∉ range x := by
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hw
    rintro ⟨t, ht⟩
    have hc := (hθ.2 t).1
    have hs := (hθ.2 t).2
    simp only [ht, sub_self, norm_zero] at hc hs
    have htidentity := Real.sin_sq_add_cos_sq (θ t)
    rw [hc, hs] at htidentity
    norm_num at htidentity
  refine ⟨hrange ▸ hp, ?_⟩
  by_contra h
  apply hw
  apply curveWinding_eq_zero_of_unbounded_component hab hx hclosed hp
  simpa only [hrange] using h

/-- Winding is invariant under any continuous family of closed loops avoiding
the basepoint. Continuity uses the uniform metric on continuous maps. -/
theorem winding_eq_of_homotopy {a b : ℝ} (hab : a < b)
    (H : Icc (0 : ℝ) 1 → C(Icc a b, Point)) (p : Point) (hH : Continuous H)
    (hclosed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩)
    (havoid : ∀ u, p ∉ range (H u)) :
    curveWinding hab.le (H ⟨1, by norm_num⟩) p =
      curveWinding hab.le (H ⟨0, by norm_num⟩) p := by
  let : PreconnectedSpace (Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  have hlc : IsLocallyConstant (fun u : Icc (0 : ℝ) 1 => curveWinding hab.le (H u) p) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro u
    obtain ⟨ε, hε, hstable⟩ := exists_winding_stability_radius hab
      (H u) p (H u).continuous (havoid u) (hclosed u)
    let W := H ⁻¹' Metric.ball (H u) ε
    refine ⟨W, Metric.isOpen_ball.preimage hH, Metric.mem_ball_self hε, ?_⟩
    intro v hv
    apply hstable (H v) (H v).continuous (hclosed v)
    intro t
    have hdist := (ContinuousMap.dist_apply_le_dist (f := H v) (g := H u) t).trans_lt hv
    simpa only [dist_eq_norm] using hdist
  exact hlc.apply_eq_of_preconnectedSpace ⟨1, by norm_num⟩ ⟨0, by norm_num⟩

/-- Winding invariance in the usual jointly continuous two-parameter formulation. -/
theorem winding_eq_of_continuous_deformation {a b : ℝ} (hab : a < b)
    (H : Icc (0 : ℝ) 1 → Icc a b → Point) (p : Point)
    (hH : Continuous (Function.uncurry H))
    (hclosed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩)
    (havoid : ∀ u, p ∉ range (H u)) :
    curveWinding hab.le (H ⟨1, by norm_num⟩) p =
      curveWinding hab.le (H ⟨0, by norm_num⟩) p := by
  let F : C(Icc (0 : ℝ) 1 × Icc a b, Point) := ⟨Function.uncurry H, hH⟩
  exact winding_eq_of_homotopy hab F.curry p F.curry.continuous hclosed havoid

/-- A sufficiently close simple Jordan boundary inherits orientation from a
radially unique reference loop; the new boundary need not be radially unique. -/
theorem oriented_jordan_of_near_radial {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hx : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b})
    (y : C(Icc a b, Point)) (p : Point) (hp : p ∉ range y)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    (hyi : InjOn y {t | (t : ℝ) < b})
    (hyr : InjOn (radialDirection p) (range y))
    (hnear : ∀ t, ‖x t - y t‖ < ‖y t - p‖) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x := by
  have hwref := winding_abs_one_of_radial_inj hab y p y.continuous hp hyc hyi hyr
  have hwEq := winding_eq_of_small_displacement hab y x p y.continuous hx hyc hclosed hnear
  have hw : |curveWinding hab.le x p| = 1 := by rw [hwEq]; exact hwref
  have hnonzero : curveWinding hab.le x p ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    norm_num at hw
  have hpint := mem_jordanInterior_of_winding_ne_zero hab.le x Γ hx hrange hclosed p hnonzero
  exact oriented_jordan_of_winding_witness hab x Γ hΓ hx hrange hclosed hinj p hpint hw

/-- Any simple Jordan endpoint of a basepoint-avoiding deformation of a radially
unique loop inherits orientation, even when it is far from the reference loop. -/
theorem oriented_jordan_of_deformation {a b : ℝ} (hab : a < b)
    (H : Icc (0 : ℝ) 1 → Icc a b → Point) (p : Point)
    (hH : Continuous (Function.uncurry H))
    (hclosed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩)
    (havoid : ∀ u, p ∉ range (H u))
    (hstart : InjOn (H ⟨0, by norm_num⟩) {t | (t : ℝ) < b})
    (hrad : InjOn (radialDirection p) (range (H ⟨0, by norm_num⟩)))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hrange : range (H ⟨1, by norm_num⟩) = Γ)
    (hinj : InjOn (H ⟨1, by norm_num⟩) {t | (t : ℝ) < b}) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation
      (H ⟨1, by norm_num⟩) := by
  let F : C(Icc (0 : ℝ) 1 × Icc a b, Point) := ⟨Function.uncurry H, hH⟩
  have hw0 := winding_abs_one_of_radial_inj hab (H ⟨0, by norm_num⟩) p
    (F.curry ⟨0, by norm_num⟩).continuous (havoid _) (hclosed _) hstart hrad
  have heq := winding_eq_of_continuous_deformation hab H p hH hclosed havoid
  have hw : |curveWinding hab.le (H ⟨1, by norm_num⟩) p| = 1 := by
    rw [heq]
    exact hw0
  have hn : curveWinding hab.le (H ⟨1, by norm_num⟩) p ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    norm_num at hw
  have hp := mem_jordanInterior_of_winding_ne_zero hab.le (H ⟨1, by norm_num⟩) Γ
    (F.curry ⟨1, by norm_num⟩).continuous hrange (hclosed _) p hn
  exact oriented_jordan_of_winding_witness hab (H ⟨1, by norm_num⟩) Γ hΓ
    (F.curry ⟨1, by norm_num⟩).continuous hrange (hclosed _) hinj p hp hw

/-- The sharp rectifiable theorem for Jordan boundaries close to a radially
unique reference loop, with no winding, convexity or radial condition on the boundary. -/
theorem jordan_isoperimetric_near_radial (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Γ) (hclosed : γ a = γ b) (hinj : InjOn γ (Ico a b))
    (y : C(Icc a b, Point)) (p : Point) (hp : p ∉ range y)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    (hyi : InjOn y {t | (t : ℝ) < b})
    (hyr : InjOn (radialDirection p) (range y))
    (hnear : ∀ t : Icc a b, ‖γ t - y t‖ < ‖y t - p‖) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (fun t : Icc a b => γ t) = Γ := by
    rw [← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (fun t : Icc a b => γ t) {t | (t : ℝ) < b} := by
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨orientation, ho⟩ := oriented_jordan_of_near_radial hab
    (fun t : Icc a b => γ t) Γ hΓ hc.domRestrict hr hclosed hi y p hp hyc hyi hyr hnear
  exact jordan_isoperimetric_rectifiable_interval γ hab hBV Γ orientation ho

/-- The full sharp theorem from a continuous deformation to a radial reference
loop. The boundary itself has no winding, convexity or radial hypothesis. -/
theorem jordan_isoperimetric_of_deformation (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hrange : γ '' Icc a b = Γ)
    (hinj : InjOn γ (Ico a b))
    (H : Icc (0 : ℝ) 1 → Icc a b → Point) (p : Point)
    (hH : Continuous (Function.uncurry H))
    (hclosed : ∀ u, H u ⟨a, le_rfl, hab.le⟩ = H u ⟨b, hab.le, le_rfl⟩)
    (havoid : ∀ u, p ∉ range (H u))
    (hstart : InjOn (H ⟨0, by norm_num⟩) {t | (t : ℝ) < b})
    (hrad : InjOn (radialDirection p) (range (H ⟨0, by norm_num⟩)))
    (hend : H ⟨1, by norm_num⟩ = fun t : Icc a b => γ t) :
    4 * Real.pi * (volume (jordanInterior Γ)).toReal ≤
      (eVariationOn γ (Icc a b)).toReal ^ 2 ∧
    (4 * Real.pi * (volume (jordanInterior Γ)).toReal =
      (eVariationOn γ (Icc a b)).toReal ^ 2 ↔
      ∃ c : Point, ∃ r : ℝ, 0 < r ∧ Γ = Metric.sphere c r) := by
  have hr : range (H ⟨1, by norm_num⟩) = Γ := by
    rw [hend, ← hrange]
    exact (image_eq_range γ (Icc a b)).symm
  have hi : InjOn (H ⟨1, by norm_num⟩) {t | (t : ℝ) < b} := by
    rw [hend]
    intro s hs t ht he
    exact Subtype.ext (hinj ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ he)
  obtain ⟨orientation, ho⟩ := oriented_jordan_of_deformation hab H p hH hclosed havoid
    hstart hrad Γ hΓ hr hi
  rw [hend] at ho
  exact jordan_isoperimetric_rectifiable_interval γ hab hBV Γ orientation ho

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.inner_pos_of_small_displacement
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_eq_of_inner_pos
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_eq_of_small_displacement
#check_upstream ClassicalTheorems.Progress.Isoperimetric.exists_winding_stability_radius
#check_upstream ClassicalTheorems.Progress.Isoperimetric.mem_jordanInterior_of_winding_ne_zero
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_eq_of_homotopy
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_eq_of_continuous_deformation
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_of_near_radial
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_of_deformation
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_near_radial
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_of_deformation

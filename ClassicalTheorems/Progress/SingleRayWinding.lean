/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.LoopCircleDeformation

/-! Automatic Jordan orientation from just one uniquely intersecting radial ray. -/

noncomputable section
open MeasureTheory Set MovingSofa
namespace ClassicalTheorems.Progress.Isoperimetric

/-- Every ray from a point in a bounded complementary component meets the boundary.
This statement does not require the boundary to be a Jordan curve. -/
theorem ray_meets_of_bounded_component (Γ : Set Point) (p v : Point)
    (hp : p ∉ Γ) (hb : Bornology.IsBounded (connectedComponentIn Γᶜ p))
    (hv : ‖v‖ = 1) : ∃ r : ℝ, 0 < r ∧ p + r • v ∈ Γ := by
  by_contra! hn
  let f : ℝ → Point := fun r => p + r • v
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have havoid : f '' Ici 0 ⊆ Γᶜ := by
    rintro _ ⟨r, hr, rfl⟩
    change 0 ≤ r at hr
    rcases hr.eq_or_lt with hr | hr
    · simpa [f, ← hr] using hp
    · exact hn r hr
  have hconn : IsPreconnected (f '' Ici 0) := isPreconnected_Ici.image f hf.continuousOn
  have hpimage : p ∈ f '' Ici 0 := ⟨0, mem_Ici.mpr le_rfl, by simp [f]⟩
  have hsub := hconn.subset_connectedComponentIn hpimage havoid
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Point)).mp hb
  let r := max R 0 + ‖p‖ + 1
  have hr : 0 < r := by dsimp [r]; linarith [le_max_right R 0, norm_nonneg p]
  have hnR : ‖f r‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR (hsub ⟨r, mem_Ici.mpr hr.le, rfl⟩)
  have htri := norm_sub_le (f r) p
  have hrad : ‖f r - p‖ = r := by simp [f, norm_smul, hv, abs_of_pos hr]
  rw [hrad] at htri
  dsimp [r] at htri
  linarith [le_max_left R 0]

/-- From every geometric Jordan interior point, radial projection covers all unit
directions, even when the boundary is nonconvex or meets a ray many times. -/
theorem jordan_radial_direction_surjective (Γ : Set Point) (p : Point)
    (hp : p ∈ jordanInterior Γ) (v : Point) (hv : ‖v‖ = 1) :
    ∃ z ∈ Γ, radialDirection p z = v := by
  obtain ⟨r, hr, hz⟩ := ray_meets_of_bounded_component Γ p v hp.1 hp.2 hv
  refine ⟨p + r • v, hz, ?_⟩
  simp [radialDirection, norm_smul, hv, abs_of_pos hr, smul_smul, hr.ne']

/-- Coordinate lifts agree with geometric radial normalization. -/
private theorem angularPoint_zero (θ : ℝ) : angularPoint θ 0 = Real.cos θ := by
  change ((Real.cos θ : ℂ) + Real.sin θ * Complex.I).re = _
  rw [Complex.add_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem angularPoint_one (θ : ℝ) : angularPoint θ 1 = Real.sin θ := by
  change ((Real.cos θ : ℂ) + Real.sin θ * Complex.I).im = _
  rw [Complex.add_im, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem radialDirection_eq_angularPoint {a b : ℝ} (x : Icc a b → Point)
    (p : Point) (θ : Icc a b → ℝ) (hθ : IsCurveAngleLift x p θ) (t : Icc a b) :
    radialDirection p (x t) = angularPoint (θ t) := by
  ext i
  fin_cases i
  · change ‖x t - p‖⁻¹ * (x t 0 - p 0) = angularPoint (θ t) 0
    rw [angularPoint_zero, (hθ.2 t).1, div_eq_mul_inv, mul_comm]
    rfl
  · change ‖x t - p‖⁻¹ * (x t 1 - p 1) = angularPoint (θ t) 1
    rw [angularPoint_one, (hθ.2 t).2, div_eq_mul_inv, mul_comm]
    rfl

/-- Equal unit directions have a whole-turn angle difference. -/
theorem cos_sub_eq_one_of_angularPoint_eq {α β : ℝ}
    (he : angularPoint α = angularPoint β) : Real.cos (α - β) = 1 := by
  have hc : Real.cos α = Real.cos β := by
    simpa only [angularPoint_zero] using
      congrArg (fun v : Point => v 0) he
  have hs : Real.sin α = Real.sin β := by
    simpa only [angularPoint_one] using
      congrArg (fun v : Point => v 1) he
  rw [Real.cos_sub, hc, hs]
  nlinarith [Real.sin_sq_add_cos_sq β]

/-- A continuous angle map covering every direction must span at least one full turn. -/
theorem angle_oscillation_ge_two_pi {a b : ℝ} (hab : a ≤ b)
    (θ : Icc a b → ℝ) (hc : Continuous θ)
    (hsurj : ∀ v : Point, ‖v‖ = 1 → ∃ t, angularPoint (θ t) = v) :
    ∃ s t, (∀ u, θ s ≤ θ u) ∧ (∀ u, θ u ≤ θ t) ∧ 2 * Real.pi ≤ θ t - θ s := by
  let : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab⟩⟩
  obtain ⟨s, _, hs⟩ := isCompact_univ.exists_isMinOn univ_nonempty hc.continuousOn
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hc.continuousOn
  refine ⟨s, t, fun u => hs (mem_univ u), fun u => ht (mem_univ u), ?_⟩
  by_contra! hn
  let φ := (θ t + θ s + 2 * Real.pi) / 2
  obtain ⟨u, hu⟩ := hsurj (angularPoint φ) (norm_angularPoint φ)
  have hcos := cos_sub_eq_one_of_angularPoint_eq hu
  have hmin : θ s ≤ θ u := hs (mem_univ u)
  have hmax : θ u ≤ θ t := ht (mem_univ u)
  have hlo : -(2 * Real.pi) < θ u - φ := by
    dsimp [φ]
    linarith
  have hhi : θ u - φ < 0 := by dsimp [φ]; linarith
  have he := (Real.cos_eq_one_iff_of_lt_of_lt hlo
    (hhi.trans (by positivity : (0 : ℝ) < 2 * Real.pi))).mp hcos
  linarith

/-- If every direction occurs and the initial direction never occurs at an
interior parameter, the lift cannot have equal endpoint values. -/
theorem angle_endpoints_ne_of_single_direction {a b : ℝ} (hab : a < b)
    (θ : Icc a b → ℝ) (hc : Continuous θ)
    (hsurj : ∀ v : Point, ‖v‖ = 1 → ∃ t, angularPoint (θ t) = v)
    (hfiber : ∀ t : Icc a b, a < (t : ℝ) → (t : ℝ) < b →
      angularPoint (θ t) ≠ angularPoint (θ ⟨a, le_rfl, hab.le⟩)) :
    θ ⟨a, le_rfl, hab.le⟩ ≠ θ ⟨b, hab.le, le_rfl⟩ := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let A : Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Icc a b := ⟨b, hab.le, le_rfl⟩
  intro hend
  change θ A = θ B at hend
  obtain ⟨s, t, hs, ht, hosc⟩ := angle_oscillation_ge_two_pi hab.le θ hc hsurj
  have hends (u : Icc a b) (he : θ u ≠ θ A) : a < (u : ℝ) ∧ (u : ℝ) < b := by
    constructor
    · apply lt_of_le_of_ne u.property.1
      intro h
      exact he (congrArg θ (show u = A from Subtype.ext h.symm))
    · apply lt_of_le_of_ne u.property.2
      intro h
      exact he ((congrArg θ (show u = B from Subtype.ext h)).trans hend.symm)
  have hext : θ s = θ A ∨ θ t = θ A := by
    by_contra! hn
    have hs' : θ s < θ A := lt_of_le_of_ne (hs A) hn.1
    have ht' : θ A < θ t := lt_of_le_of_ne (ht A) hn.2.symm
    rcases le_total s t with hst | hts
    · obtain ⟨u, hu, he⟩ := intermediate_value_Ioo hst hc.continuousOn ⟨hs', ht'⟩
      exact hfiber u (lt_of_le_of_lt s.property.1 hu.1)
        (lt_of_lt_of_le hu.2 t.property.2) (congrArg angularPoint he)
    · obtain ⟨u, hu, he⟩ := intermediate_value_Ioo' hts hc.continuousOn ⟨hs', ht'⟩
      exact hfiber u (lt_of_le_of_lt t.property.1 hu.1)
        (lt_of_lt_of_le hu.2 s.property.2) (congrArg angularPoint he)
  rcases hext with hext | hext
  · have htarget : θ A + 2 * Real.pi ∈ Icc (θ A) (θ t) := by
      rw [hext] at hosc
      constructor <;> linarith [Real.pi_pos]
    obtain ⟨u, _, he⟩ := intermediate_value_Icc (show A ≤ t from t.property.1)
      hc.continuousOn htarget
    have hu := hends u (by rw [he]; linarith [Real.pi_pos])
    apply hfiber u hu.1 hu.2
    simp [angularPoint, he, A]
  · have htarget : θ A - 2 * Real.pi ∈ Icc (θ s) (θ A) := by
      rw [hext] at hosc
      constructor <;> linarith [Real.pi_pos]
    obtain ⟨u, _, he⟩ := intermediate_value_Icc' (show A ≤ s from s.property.1)
      hc.continuousOn htarget
    have hu := hends u (by rw [he]; linarith [Real.pi_pos])
    apply hfiber u hu.1 hu.2
    simp [angularPoint, he, A]

/-- A uniquely visited direction in a surjective closed angular path forces
exactly one full turn, without injectivity in any other direction. -/
theorem angle_increment_eq_full_turn_of_single_direction {a b : ℝ} (hab : a < b)
    (θ : Icc a b → ℝ) (hc : Continuous θ)
    (hsurj : ∀ v : Point, ‖v‖ = 1 → ∃ t, angularPoint (θ t) = v)
    (hfiber : ∀ t : Icc a b, a < (t : ℝ) → (t : ℝ) < b →
      angularPoint (θ t) ≠ angularPoint (θ ⟨a, le_rfl, hab.le⟩))
    (hclosed : angularPoint (θ ⟨b, hab.le, le_rfl⟩) =
      angularPoint (θ ⟨a, le_rfl, hab.le⟩)) :
    θ ⟨b, hab.le, le_rfl⟩ - θ ⟨a, le_rfl, hab.le⟩ = 2 * Real.pi ∨
      θ ⟨b, hab.le, le_rfl⟩ - θ ⟨a, le_rfl, hab.le⟩ = -(2 * Real.pi) := by
  let : Fact (a ≤ b) := ⟨hab.le⟩
  let A : Icc a b := ⟨a, le_rfl, hab.le⟩
  let B : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hne := angle_endpoints_ne_of_single_direction hab θ hc hsurj hfiber
  have hcos := cos_sub_eq_one_of_angularPoint_eq hclosed
  have hupper : θ B - θ A ≤ 2 * Real.pi := by
    by_contra! hn
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo (show A ≤ B from hab.le)
      hc.continuousOn (show θ A + 2 * Real.pi ∈ Ioo (θ A) (θ B) by
        constructor <;> linarith [Real.pi_pos])
    apply hfiber t ht.1 ht.2
    simp [angularPoint, he, A]
  have hlower : -(2 * Real.pi) ≤ θ B - θ A := by
    by_contra! hn
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo' (show A ≤ B from hab.le)
      hc.continuousOn (show θ A - 2 * Real.pi ∈ Ioo (θ B) (θ A) by
        constructor <;> linarith [Real.pi_pos])
    apply hfiber t ht.1 ht.2
    simp [angularPoint, he, A]
  by_contra! hn
  have hz := (Real.cos_eq_one_iff_of_lt_of_lt
    (lt_of_le_of_ne hlower hn.2.symm) (lt_of_le_of_ne hupper hn.1)).mp hcos
  exact hne (sub_eq_zero.mp hz).symm

/-- One ray meeting the boundary exactly once is enough for automatic unit winding.
Other rays may meet it repeatedly, and the interior need not be convex. -/
theorem winding_abs_one_of_single_ray {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (p : Point)
    (hc : Continuous x) (hrange : range x = Γ) (hp : p ∈ jordanInterior Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b})
    (hunique : ∀ z ∈ Γ, radialDirection p z =
      radialDirection p (x ⟨a, le_rfl, hab.le⟩) → z = x ⟨a, le_rfl, hab.le⟩) :
    |curveWinding hab.le x p| = 1 := by
  have havoid : p ∉ range x := hrange ▸ hp.1
  obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab hc havoid
  have hsurj (v : Point) (hv : ‖v‖ = 1) : ∃ t, angularPoint (θ t) = v := by
    obtain ⟨z, hz, he⟩ := jordan_radial_direction_surjective Γ p hp v hv
    rw [← hrange] at hz
    obtain ⟨t, rfl⟩ := hz
    exact ⟨t, (radialDirection_eq_angularPoint x p θ hθ t).symm.trans he⟩
  have hfiber (t : Icc a b) (ha : a < (t : ℝ)) (hb : (t : ℝ) < b) :
      angularPoint (θ t) ≠ angularPoint (θ ⟨a, le_rfl, hab.le⟩) := by
    intro he
    have hdir : radialDirection p (x t) = radialDirection p (x ⟨a, le_rfl, hab.le⟩) := by
      rw [radialDirection_eq_angularPoint x p θ hθ t,
        radialDirection_eq_angularPoint x p θ hθ ⟨a, le_rfl, hab.le⟩, he]
    have hxt := hunique (x t) (hrange ▸ mem_range_self t) hdir
    have hta := hinj hb hab hxt
    have hval := congrArg Subtype.val hta
    exact ha.ne' hval
  have hend : angularPoint (θ ⟨b, hab.le, le_rfl⟩) =
      angularPoint (θ ⟨a, le_rfl, hab.le⟩) := by
    rw [← radialDirection_eq_angularPoint x p θ hθ _,
      ← radialDirection_eq_angularPoint x p θ hθ _, hclosed]
  have hturn := angle_increment_eq_full_turn_of_single_direction hab θ hθ.1 hsurj hfiber hend
  rw [hθ.curveWinding_eq hab.le]
  rcases hturn with hturn | hturn <;> rw [hturn] <;> field_simp <;> simp

/-- A single uniquely intersecting ray through the initial boundary point determines
the global Jordan orientation. -/
theorem oriented_jordan_of_single_ray {a b : ℝ} (hab : a < b)
    (x : Icc a b → Point) (Γ : Set Point) (hΓ : IsJordanCurve Γ)
    (hc : Continuous x) (hrange : range x = Γ)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hinj : InjOn x {t | (t : ℝ) < b}) (p : Point) (hp : p ∈ jordanInterior Γ)
    (hunique : ∀ z ∈ Γ, radialDirection p z =
      radialDirection p (x ⟨a, le_rfl, hab.le⟩) → z = x ⟨a, le_rfl, hab.le⟩) :
    ∃ orientation : Bool, IsOrientedJordanParametrization hab.le Γ orientation x :=
  oriented_jordan_of_winding_witness hab x Γ hΓ hc hrange hclosed hinj p hp
    (winding_abs_one_of_single_ray hab x Γ p hc hrange hp hclosed hinj hunique)

/-- Full sharp isoperimetry and circle characterization from one uniquely
intersecting ray, with no convexity, global radial injectivity or winding input. -/
theorem jordan_isoperimetric_single_ray (γ : ℝ → Point)
    {a b : ℝ} (hab : a < b) (hBV : BoundedVariationOn γ (Icc a b))
    (Γ : Set Point) (hΓ : IsJordanCurve Γ) (hc : ContinuousOn γ (Icc a b))
    (hrange : γ '' Icc a b = Γ) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (p : Point) (hp : p ∈ jordanInterior Γ)
    (hunique : ∀ z ∈ Γ, radialDirection p z = radialDirection p (γ a) → z = γ a) :
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
  exact jordan_isoperimetric_of_winding_witness γ hab hBV Γ hΓ hc hrange hclosed hinj p hp
    (winding_abs_one_of_single_ray hab (fun t : Icc a b => γ t) Γ p
      hc.domRestrict hr hp hclosed hi hunique)

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.ray_meets_of_bounded_component
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_radial_direction_surjective
#check_upstream ClassicalTheorems.Progress.Isoperimetric.radialDirection_eq_angularPoint
#check_upstream ClassicalTheorems.Progress.Isoperimetric.cos_sub_eq_one_of_angularPoint_eq
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angle_oscillation_ge_two_pi
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angle_endpoints_ne_of_single_direction
#check_upstream ClassicalTheorems.Progress.Isoperimetric.angle_increment_eq_full_turn_of_single_direction
#check_upstream ClassicalTheorems.Progress.Isoperimetric.winding_abs_one_of_single_ray
#check_upstream ClassicalTheorems.Progress.Isoperimetric.oriented_jordan_of_single_ray
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_single_ray

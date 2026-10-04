/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.IsoperimetricC1
import Mathlib.Topology.Order.Compact

/-! Exact arc-length reparametrization and circle rigidity for regular C¹ curves.
No constant-speed assumption is made about the original parametrization. -/

noncomputable section
open MeasureTheory Set
namespace ClassicalTheorems.Progress.Isoperimetric

theorem regular_c1_reparametrization (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ 1 φ ∧ StrictMono φ ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖deriv (γ ∘ φ) t‖ = ∫ s in (0 : ℝ)..1, ‖deriv γ s‖ := by
  have hs := hγ.continuous_deriv_one.norm
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (by exact ⟨0, by norm_num⟩ : (Icc (0 : ℝ) 1).Nonempty) hs.continuousOn
  let m := ‖deriv γ a‖
  have hm : 0 < m := norm_pos_iff.mpr (hregular a ha)
  let w := fun t => max ‖deriv γ t‖ m
  have hw : Continuous w := hs.max continuous_const
  have hw_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : w t = ‖deriv γ t‖ :=
    max_eq_left (hmin ht)
  obtain ⟨φ, hφ, hmono, hφ0, hφ1, hdφ⟩ := positive_density_reparametrization w hw m hm
    (fun t => le_max_right _ _)
  have hφmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : φ t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · simpa only [hφ0] using hmono.monotone ht.1
    · simpa only [hφ1] using hmono.monotone ht.2
  have hL : 0 ≤ ∫ s in (0 : ℝ)..1, ‖deriv γ s‖ :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun s => norm_nonneg _)
  have hLid : (∫ s in (0 : ℝ)..1, w s) = ∫ s in (0 : ℝ)..1, ‖deriv γ s‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hw_eq t (by simpa using ht)
  refine ⟨φ, hφ, hmono, hφ0, hφ1, ?_⟩
  intro t ht
  have hp : 0 < ‖deriv γ (φ t)‖ := norm_pos_iff.mpr (hregular _ (hφmem t ht))
  rw [deriv_reparam γ hγ φ hφ, (hdφ t).deriv, hLid, hw_eq _ (hφmem t ht),
    norm_smul, Real.norm_of_nonneg (div_nonneg hL hp.le), div_mul_cancel₀ _ hp.ne']

theorem signed_area_perimeter_equality_regular (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ)
    (hclosed : γ 0 = γ 1) (hsimple : InjOn γ (Ico 0 1))
    (hregular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (heq : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2) :
    ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ γ '' Icc 0 1 = Metric.sphere c r := by
  obtain ⟨φ, hφ, hmono, hφ0, hφ1, hspeed⟩ := regular_c1_reparametrization γ hγ hregular
  have hinterval : φ '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    rw [hφ.continuous.image_Icc_of_strictMono hmono, hφ0, hφ1]
  have hIco : MapsTo φ (Ico (0 : ℝ) 1) (Ico (0 : ℝ) 1) := by
    intro t ht
    constructor
    · simpa only [hφ0] using hmono.monotone ht.1
    · simpa only [hφ1] using hmono ht.2
  have hδ : ContDiff ℝ 1 (γ ∘ φ) := hγ.comp hφ
  have hcδ : (γ ∘ φ) 0 = (γ ∘ φ) 1 := by simpa [hφ0, hφ1] using hclosed
  have hsδ : InjOn (γ ∘ φ) (Ico 0 1) := by
    intro a ha b hb he
    exact hmono.injective (hsimple (hIco ha) (hIco hb) he)
  have henergy : (∫ t in (0 : ℝ)..1, ‖deriv (γ ∘ φ) t‖ ^ 2) =
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
    calc
      _ = ∫ _t in (0 : ℝ)..1, (∫ s in (0 : ℝ)..1, ‖deriv γ s‖) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ‖deriv (γ ∘ φ) t‖ ^ 2 = _
        rw [hspeed t (by simpa using ht)]
      _ = _ := by simp
  have heδ : 4 * Real.pi *
      (∫ t in (0 : ℝ)..1, ((γ ∘ φ) t).re * (deriv (γ ∘ φ) t).im) =
      ∫ t in (0 : ℝ)..1, ‖deriv (γ ∘ φ) t‖ ^ 2 := by
    change 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ (φ t)).re * (deriv (γ ∘ φ) t).im) = _
    rw [reparam_signed_area γ hγ φ hφ hφ0 hφ1, henergy, heq]
  obtain ⟨c, r, hr, hcircle⟩ := area_energy_equality_circle (γ ∘ φ) hδ hcδ hsδ heδ
  rw [image_comp, hinterval] at hcircle
  exact ⟨c, r, hr, hcircle⟩

/-- The perimeter bound and circle rigidity for an arbitrary regular C¹
positively oriented Jordan parametrization. -/
theorem jordan_isoperimetric_regular (D : Set ℂ) (γ : ℝ → ℂ)
    (hDomain : IsOpen D) (hBounded : Bornology.IsBounded D) (hConnected : IsConnected D)
    (hBoundary : frontier D = γ '' Icc 0 1)
    (hCurve : ContDiff ℝ 1 γ) (hClosed : γ 0 = γ 1)
    (hSimple : InjOn γ (Ico 0 1))
    (hRegular : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hPositive : ∀ z ∈ D,
      (∫ t in (0 : ℝ)..1, (deriv γ t / (γ t - z)).im) = 2 * Real.pi) :
    4 * Real.pi * (volume D).toReal ≤ (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 ∧
      (4 * Real.pi * (volume D).toReal = (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 →
        ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ frontier D = Metric.sphere c r) := by
  refine ⟨jordan_isoperimetric_c1 D γ hDomain hBounded hConnected hBoundary
    hCurve hClosed hSimple hPositive, ?_⟩
  intro heq
  have he : 4 * Real.pi * (∫ t in (0 : ℝ)..1, (γ t).re * (deriv γ t).im) =
      (∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ^ 2 := by
    rwa [Green.complex_signedArea_eq_domain_area D γ hDomain hBounded hConnected
      hBoundary hCurve hClosed hSimple hPositive]
  obtain ⟨c, r, hr, hcircle⟩ := signed_area_perimeter_equality_regular γ hCurve hClosed
    hSimple hRegular he
  exact ⟨c, r, hr, hBoundary.trans hcircle⟩

end ClassicalTheorems.Progress.Isoperimetric
#check_upstream ClassicalTheorems.Progress.Isoperimetric.regular_c1_reparametrization
#check_upstream ClassicalTheorems.Progress.Isoperimetric.jordan_isoperimetric_regular

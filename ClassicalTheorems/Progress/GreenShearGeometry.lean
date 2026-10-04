/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.Green
import MovingSofa.Curve.Jordan.WindingLocalConstancy
import MovingSofa.Curve.Jordan.WindingLifts
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting

/-! Global geometry of the small perturbations used in the shear reduction of Green’s theorem. -/
noncomputable section
open Set Function
open scoped NNReal
namespace ClassicalTheorems.Progress.Green

/-- Adding a map with Lipschitz constant below one to the identity gives a
homeomorphism. Surjectivity follows from the contraction fixed-point theorem. -/
theorem exists_homeomorph_add_of_lipschitz (g : ℂ → ℂ) (K : ℝ≥0)
    (hg : LipschitzWith K g) (hK : K < 1) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z, e z = z + g z := by
  have hAnti : AntilipschitzWith (1 - K)⁻¹ (fun z => z + g z) := by
    simpa using AntilipschitzWith.id.add_lipschitzWith hg (by simpa using hK)
  have hSurj : Surjective (fun z => z + g z) := by
    intro y
    have hContract : ContractingWith K (fun z => y - g z) := by
      refine ⟨hK, ?_⟩
      simpa only [zero_add, sub_eq_add_neg, Pi.neg_apply] using (LipschitzWith.const y).add hg.neg
    let z := ContractingWith.fixedPoint (fun z => y - g z) hContract
    have hz : y - g z = z := hContract.fixedPoint_isFixedPt
    exact ⟨z, eq_sub_iff_add_eq.mp hz.symm⟩
  let e := Equiv.ofBijective (fun z => z + g z) ⟨hAnti.injective, hSurj⟩
  have hc : Continuous (fun z => z + g z) := continuous_id.add hg.continuous
  exact ⟨e.toHomeomorphOfIsInducing (hAnti.isInducing hc), fun _ => rfl⟩


/-- Two closed loops with everywhere positive relative dot product have equal winding.
The continuous principal relative argument supplies the correction to an angle lift. -/
theorem complex_winding_eq_of_relative_dot_pos (γ η : ℝ → ℂ) (p q : ℂ)
    (hγ : Continuous γ) (hη : Continuous η) (hγclosed : γ 0 = γ 1)
    (hηclosed : η 0 = η 1) (hp : p ∉ γ '' Icc 0 1)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < (starRingEnd ℂ (γ t - p) * (η t - q)).re) :
    MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (η t))
      (Complex.orthonormalBasisOneI.repr q) =
    MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (γ t))
      (Complex.orthonormalBasisOneI.repr p) := by
  let e := Complex.orthonormalBasisOneI.repr
  let x : Icc (0 : ℝ) 1 → MovingSofa.Point := fun t => e (γ t)
  let y : Icc (0 : ℝ) 1 → MovingSofa.Point := fun t => e (η t)
  have hx : Continuous x := e.continuous.comp (hγ.comp continuous_subtype_val)
  have hp' : e p ∉ range x := by
    rintro ⟨t, ht⟩
    exact hp ⟨t, t.property, e.injective ht⟩
  obtain ⟨θ, hθ⟩ := MovingSofa.exists_curveAngleLift_of_avoids (by norm_num : (0 : ℝ) < 1) hx hp'
  let z : Icc (0 : ℝ) 1 → ℂ := fun t => γ t - p
  let w : Icc (0 : ℝ) 1 → ℂ := fun t => η t - q
  let δ : Icc (0 : ℝ) 1 → ℝ := fun t => Complex.arg (starRingEnd ℂ (z t) * w t)
  have hz : Continuous z := (hγ.comp continuous_subtype_val).sub continuous_const
  have hw : Continuous w := (hη.comp continuous_subtype_val).sub continuous_const
  have hδ : Continuous δ := MovingSofa.continuous_arg_conj_mul_of_re_pos hz hw
    (fun t => hpos t t.property)
  have hθ' : MovingSofa.IsCurveAngleLift y (e q) (fun t => θ t + δ t) := by
    refine ⟨hθ.1.add hδ, fun t => ?_⟩
    have hprod : starRingEnd ℂ (z t) * w t ≠ 0 := by
      intro hzero
      have := hpos t t.property
      change 0 < (starRingEnd ℂ (z t) * w t).re at this
      simp [hzero] at this
    have hzne : z t ≠ 0 := fun hzero => hprod (by simp [hzero])
    have hwne : w t ≠ 0 := fun hzero => hprod (by simp [hzero])
    have hcos : Real.cos (θ t) = (z t).re / ‖z t‖ := by
      simpa [x, z, e, ← map_sub] using (hθ.2 t).1
    have hsin : Real.sin (θ t) = (z t).im / ‖z t‖ := by
      simpa [x, z, e, ← map_sub] using (hθ.2 t).2
    have hrot := MovingSofa.normalized_complex_rotation_by_relative_arg hzne hwne hcos hsin
    simpa [y, w, δ, e, ← map_sub] using hrot
  have hend : δ ⟨0, le_rfl, by norm_num⟩ = δ ⟨1, by norm_num, le_rfl⟩ := by
    simp only [δ, z, w, hγclosed, hηclosed]
  rw [hθ'.curveWinding_eq (by norm_num : (0 : ℝ) ≤ 1),
    hθ.curveWinding_eq (by norm_num : (0 : ℝ) ≤ 1), hend]
  ring

/-- A perturbation with Lipschitz constant below one keeps every radial vector
in a positive relative half-plane. -/
theorem positive_relative_dot_of_lipschitz (g : ℂ → ℂ) (K : ℝ≥0)
    (hg : LipschitzWith K g) (hK : K < 1) (z p : ℂ) (hzp : z ≠ p) :
    0 < (starRingEnd ℂ (z - p) * ((z + g z) - (p + g p))).re := by
  have hv : 0 < ‖z - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have hKr : (K : ℝ) < 1 := by exact_mod_cast hK
  have hLip : ‖g z - g p‖ ≤ (K : ℝ) * ‖z - p‖ := by
    simpa only [dist_eq_norm] using hg.dist_le_mul z p
  have hab : |(starRingEnd ℂ (z - p) * (g z - g p)).re| ≤
      ‖z - p‖ * ‖g z - g p‖ := by
    calc
      _ ≤ ‖starRingEnd ℂ (z - p) * (g z - g p)‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, Complex.norm_conj]
  have hself : (starRingEnd ℂ (z - p) * (z - p)).re = ‖z - p‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  rw [show (z + g z) - (p + g p) = (z - p) + (g z - g p) by ring,
    mul_add, Complex.add_re, hself]
  have hLower := neg_le_of_abs_le hab
  have hMul := mul_le_mul_of_nonneg_left hLip (norm_nonneg (z - p))
  have hStrict := mul_lt_mul_of_pos_right hKr (sq_pos_of_pos hv)
  nlinarith


/-- A small Lipschitz perturbation preserves a closed loop's winding about
its correspondingly moved basepoint. -/
theorem complex_winding_add_of_lipschitz (γ : ℝ → ℂ) (g : ℂ → ℂ) (K : ℝ≥0)
    (hγ : Continuous γ) (hclosed : γ 0 = γ 1) (hg : LipschitzWith K g) (hK : K < 1)
    (p : ℂ) (hp : p ∉ γ '' Icc 0 1) :
    MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (γ t + g (γ t)))
      (Complex.orthonormalBasisOneI.repr (p + g p)) =
    MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
      (fun t : Icc (0 : ℝ) 1 => Complex.orthonormalBasisOneI.repr (γ t))
      (Complex.orthonormalBasisOneI.repr p) := by
  apply complex_winding_eq_of_relative_dot_pos γ (fun t => γ t + g (γ t)) p (p + g p)
    hγ (hγ.add (hg.continuous.comp hγ)) hclosed (by rw [hclosed]) hp
  intro t ht
  apply positive_relative_dot_of_lipschitz g K hg hK (γ t) p
  intro heq
  exact hp ⟨t, ht, heq⟩

end ClassicalTheorems.Progress.Green
#check_upstream ClassicalTheorems.Progress.Green.exists_homeomorph_add_of_lipschitz

#check_upstream ClassicalTheorems.Progress.Green.complex_winding_eq_of_relative_dot_pos
#check_upstream ClassicalTheorems.Progress.Green.positive_relative_dot_of_lipschitz

#check_upstream ClassicalTheorems.Progress.Green.complex_winding_add_of_lipschitz

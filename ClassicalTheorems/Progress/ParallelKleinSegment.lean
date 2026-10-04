/-
Upstream HOL Light:
Copyright (c) University of Cambridge 1998.
Copyright (c) John Harrison and others 1998-2012.

Lean adaptation:
Copyright 2026 Michael Brackx
SPDX-License-Identifier: BSD-2-Clause

Manual mathematical adaptation of the model argument in John Harrison’s HOL Light
Multivariate/tarski.ml and 100/independence.ml (with credit to Tim Makarios).
The Lean proofs, including the Lorentz-coordinate construction, are verified anew.
See NOTICE and vendor/hol-light-port/LICENSE for attribution and license terms.
-/
import ClassicalTheorems.Progress.ParallelKleinFiveSegment

/-! Segment construction in the Klein disk via the unit Lorentz hyperboloid. -/

namespace ClassicalTheorems.Progress.Parallel.Klein

noncomputable section

/-- A unit Lorentz vector with positive inner product with a future unit vector is future. -/
theorem lorentz_time_pos (A C : ℝ × ℂ) (hA : lorentz A A = 1)
    (hC : lorentz C C = 1) (hAt : 0 < A.1) (hAC : 0 < lorentz A C) : 0 < C.1 := by
  by_contra hct
  have hct' : C.1 ≤ 0 := le_of_not_gt hct
  let p := A.1*C.1
  let d := A.2.re*C.2.re+A.2.im*C.2.im
  let x := A.2.re^2+A.2.im^2
  let y := C.2.re^2+C.2.im^2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hpa : p ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hAt.le hct'
  have hd : d < p := by dsimp [d,p]; unfold lorentz at hAC; linarith
  have hsmall : p^2 < d^2 := by nlinarith
  have hcs : d^2 ≤ x*y := by
    dsimp [d,x,y]
    nlinarith [sq_nonneg (A.2.re*C.2.im-A.2.im*C.2.re)]
  have hap : A.1^2 = x+1 := by unfold lorentz at hA; dsimp [x]; nlinarith
  have hcp : C.1^2 = y+1 := by unfold lorentz at hC; dsimp [y]; nlinarith
  have hproduct : p^2 = (x+1)*(y+1) := by
    dsimp [p]
    rw [mul_pow,hap,hcp]
  nlinarith

/-- Projecting a future unit Lorentz vector produces a point of the open disk. -/
def ofLorentz (A : ℝ × ℂ) (hu : lorentz A A = 1) (ht : 0 < A.1) : Disk :=
  ⟨(1/A.1) • A.2, by
    simp only [Complex.normSq_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    have hsum : A.2.re^2+A.2.im^2 = A.1^2-1 := by unfold lorentz at hu; nlinarith
    have he : (1/A.1*A.2.re)^2+(1/A.1*A.2.im)^2 = (A.1^2-1)/A.1^2 := by
      rw [←hsum]
      field_simp
    have hineq : (1/A.1*A.2.re)^2+(1/A.1*A.2.im)^2 < 1 := by
      rw [he]
      apply (div_lt_one (sq_pos_of_pos ht)).mpr
      linarith
    simpa only [pow_two] using hineq⟩

/-- Homogeneous normalization reverses the hyperboloid projection. -/
theorem lift_ofLorentz (A : ℝ × ℂ) (hu : lorentz A A = 1) (ht : 0 < A.1) :
    lift (ofLorentz A hu ht) = A := by
  let a := ofLorentz A hu ht
  have hsa := sigma_sq a
  have hsum : A.2.re^2+A.2.im^2 = A.1^2-1 := by unfold lorentz at hu; nlinarith
  have hsigmasq : sigma a ^ 2 = (1/A.1)^2 := by
    rw [hsa]
    simp only [a,ofLorentz,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    field_simp [ne_of_gt ht]
    nlinarith [hsum]
  have hsigma : sigma a = 1/A.1 := by
    have h1 : 0 < sigma a := sigma_pos a
    have h2 : 0 < 1/A.1 := one_div_pos.mpr ht
    nlinarith [hsigmasq]
  have htime : 1/sigma a = A.1 := by rw [hsigma]; field_simp
  apply Prod.ext
  · exact htime
  · change (1/sigma a) • ((1/A.1) • A.2) = A.2
    rw [htime,smul_smul,mul_one_div_cancel (ne_of_gt ht),one_smul]

end
end ClassicalTheorems.Progress.Parallel.Klein

#check_upstream ClassicalTheorems.Progress.Parallel.Klein.lorentz_time_pos
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.lift_ofLorentz

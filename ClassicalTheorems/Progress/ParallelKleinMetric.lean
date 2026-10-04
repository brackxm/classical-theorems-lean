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
import ClassicalTheorems.Progress.ParallelKlein

/-! Hyperbolic congruence in the Klein disk and its elementary metric properties. -/

namespace ClassicalTheorems.Progress.Parallel.Klein

open Set Module
noncomputable section

/-- The positive homogeneous normalization factor. -/
def sigma (a : Disk) : ℝ := Real.sqrt (1 - Complex.normSq a.val)

theorem sigma_pos (a : Disk) : 0 < sigma a :=
  Real.sqrt_pos.mpr (sub_pos.mpr a.property)

theorem sigma_sq (a : Disk) : sigma a ^ 2 = 1 - a.val.re^2 - a.val.im^2 := by
  rw [sigma, Real.sq_sqrt (sub_nonneg.mpr a.property.le)]
  simp [Complex.normSq_apply, pow_two]
  ring

/-- The hyperbolic cosine of the distance; equality defines segment congruence. -/
def coshDist (a b : Disk) : ℝ :=
  (1 - a.val.re*b.val.re - a.val.im*b.val.im) / (sigma a * sigma b)

def congruent (a b c d : Disk) : Prop := coshDist a b = coshDist c d

theorem coshDist_comm (a b : Disk) : coshDist a b = coshDist b a := by
  unfold coshDist
  congr 1 <;> ring

theorem coshDist_self (a : Disk) : coshDist a a = 1 := by
  unfold coshDist
  apply (div_eq_one_iff_eq (ne_of_gt (mul_pos (sigma_pos a) (sigma_pos a)))).mpr
  nlinarith [sigma_sq a]

/-- Cauchy-Schwarz on the unit upper hemisphere, written as a sum of squares. -/
theorem one_le_coshDist (a b : Disk) : 1 ≤ coshDist a b := by
  apply (le_div_iff₀ (mul_pos (sigma_pos a) (sigma_pos b))).mpr
  nlinarith [sigma_sq a, sigma_sq b, sq_nonneg (a.val.re-b.val.re),
    sq_nonneg (a.val.im-b.val.im), sq_nonneg (sigma a-sigma b)]

theorem coshDist_eq_one (a b : Disk) : coshDist a b = 1 ↔ a = b := by
  constructor
  · intro h
    have he := (div_eq_one_iff_eq (ne_of_gt (mul_pos (sigma_pos a) (sigma_pos b)))).mp h
    have hr : a.val.re = b.val.re := by
      nlinarith [sigma_sq a, sigma_sq b, sq_nonneg (a.val.re-b.val.re),
        sq_nonneg (a.val.im-b.val.im), sq_nonneg (sigma a-sigma b)]
    have hi : a.val.im = b.val.im := by
      nlinarith [sigma_sq a, sigma_sq b, sq_nonneg (a.val.re-b.val.re),
        sq_nonneg (a.val.im-b.val.im), sq_nonneg (sigma a-sigma b)]
    exact Subtype.ext (Complex.ext hr hi)
  · rintro rfl; exact coshDist_self a

theorem congruence_reversal (a b : Disk) : congruent a b b a := coshDist_comm a b

theorem congruence_transitivity (a b p q r s : Disk)
    (h1 : congruent a b p q) (h2 : congruent a b r s) : congruent p q r s := h1.symm.trans h2

theorem congruence_identity (a b c : Disk) (h : congruent a b c c) : a = b := by
  exact (coshDist_eq_one a b).mp (h.trans (coshDist_self c))

/-- Homogeneous Lorentz coordinates for the disk. -/
def lift (a : Disk) : ℝ × ℂ := (1/sigma a, (1/sigma a) • a.val)

def lorentz (A B : ℝ × ℂ) : ℝ :=
  A.1*B.1 - A.2.re*B.2.re - A.2.im*B.2.im

theorem lift_time_pos (a : Disk) : 0 < (lift a).1 := one_div_pos.mpr (sigma_pos a)

theorem lift_lorentz (a b : Disk) : lorentz (lift a) (lift b) = coshDist a b := by
  simp only [lorentz,lift,coshDist,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  field_simp

theorem lift_lorentz_self (a : Disk) : lorentz (lift a) (lift a) = 1 := by
  rw [lift_lorentz,coshDist_self]

theorem lift_projection (a : Disk) : (lift a).1 • a.val = (lift a).2 := rfl

theorem lift_space_injective : Function.Injective (fun a : Disk ↦ (lift a).2) := by
  intro a b h
  change (lift a).2 = (lift b).2 at h
  have ha := lift_lorentz_self a
  have hb := lift_lorentz_self b
  unfold lorentz at ha hb
  rw [h] at ha
  have ht : (lift a).1 = (lift b).1 := by
    nlinarith [lift_time_pos a,lift_time_pos b]
  apply Subtype.ext
  apply smul_right_injective ℂ (ne_of_gt (lift_time_pos a))
  change (lift a).1 • a.val = (lift a).1 • b.val
  calc (lift a).1 • a.val = (lift a).2 := rfl
       _ = (lift b).2 := h
       _ = (lift b).1 • b.val := rfl
       _ = (lift a).1 • b.val := by rw [ht]

theorem inner_complex (x y : ℂ) : inner ℝ x y = x.re*y.re+x.im*y.im := by
  change y.re*x.re-y.im*(-x.im) = _
  ring

/-- Equidistant loci in Klein coordinates are affine lines. -/
theorem equidistant_collinear (p q a b c : Disk) (hpq : p ≠ q)
    (ha : congruent a p a q) (hb : congruent b p b q) (hc : congruent c p c q) :
    Collinear ℝ ({a.val,b.val,c.val} : Set ℂ) := by
  let n : ℂ := (lift p).2 - (lift q).2
  have hn : n ≠ 0 := by
    intro hzero
    exact hpq (lift_space_injective (sub_eq_zero.mp hzero))
  have heq : ∀ x : Disk, congruent x p x q →
      inner ℝ n x.val = (lift p).1 - (lift q).1 := by
    intro x hx
    change coshDist x p = coshDist x q at hx
    rw [← lift_lorentz,← lift_lorentz] at hx
    simp only [lorentz,lift,Complex.smul_re,Complex.smul_im,smul_eq_mul] at hx
    have htime := lift_time_pos x
    change 0 < 1/sigma x at htime
    rw [inner_complex]
    simp only [n,Complex.sub_re,Complex.sub_im]
    simp only [lift,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    have he : (1/sigma x) *
        (((1/sigma p)*p.val.re-(1/sigma q)*q.val.re)*x.val.re +
         ((1/sigma p)*p.val.im-(1/sigma q)*q.val.im)*x.val.im -
         ((1/sigma p)-(1/sigma q))) = 0 := by nlinarith [hx]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (ne_of_gt htime))
  let W : Submodule ℝ ℂ := (ℝ ∙ n)ᗮ
  have : Fact (finrank ℝ ℂ = 1+1) := ⟨Complex.finrank_real_complex⟩
  have hdim : finrank ℝ W = 1 := Submodule.finrank_orthogonal_span_singleton hn
  have hm : ∀ x ∈ ({a.val,b.val,c.val} : Set ℂ), (a.val -ᵥ x : ℂ) ∈ W := by
    intro x hx
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simp only [mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with hxa | hxb | hxc
    · subst x; simp
    · subst x; change inner ℝ n (a.val-b.val) = 0
      rw [inner_sub_right,heq a ha,heq b hb,sub_self]
    · subst x; change inner ℝ n (a.val-c.val) = 0
      rw [inner_sub_right,heq a ha,heq c hc,sub_self]
  have hspan : vectorSpan ℝ ({a.val,b.val,c.val} : Set ℂ) ≤ W := by
    rw [vectorSpan_eq_span_vsub_set_left ℝ (by simp : a.val ∈ ({a.val,b.val,c.val} : Set ℂ)),
      Submodule.span_le]
    rintro _ ⟨x,hx,rfl⟩
    exact hm x hx
  rw [collinear_iff_finrank_le_one]
  exact (Submodule.finrank_mono hspan).trans hdim.le

theorem upper_dimension (a b c p q : Disk) (hpq : p ≠ q)
    (ha : congruent a p a q) (hb : congruent b p b q) (hc : congruent c p c q) :
    between a b c ∨ between b c a ∨ between c a b :=
  (equidistant_collinear p q a b c hpq ha hb hc).wbtw_or_wbtw_or_wbtw

end

end ClassicalTheorems.Progress.Parallel.Klein

#check_upstream ClassicalTheorems.Progress.Parallel.Klein.congruence_identity
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.one_le_coshDist
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.lift_space_injective
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.upper_dimension

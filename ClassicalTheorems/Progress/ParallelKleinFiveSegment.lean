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
import ClassicalTheorems.Progress.ParallelKleinMetric

/-! The five-segment axiom of the Klein disk via homogeneous Lorentz coordinates. -/

namespace ClassicalTheorems.Progress.Parallel.Klein

open AffineMap Set
noncomputable section

theorem lorentz_comm (A B : ℝ × ℂ) : lorentz A B = lorentz B A := by unfold lorentz; ring

theorem lorentz_add_left (A B C : ℝ × ℂ) :
    lorentz (A+B) C = lorentz A C + lorentz B C := by
  simp only [lorentz,Prod.fst_add,Prod.snd_add,Complex.add_re,Complex.add_im]
  ring

theorem lorentz_smul_left (r : ℝ) (A B : ℝ × ℂ) :
    lorentz (r • A) B = r * lorentz A B := by
  simp only [lorentz,Prod.smul_fst,Prod.smul_snd,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem lorentz_add_right (A B C : ℝ × ℂ) :
    lorentz A (B+C) = lorentz A B + lorentz A C := by
  rw [lorentz_comm,lorentz_add_left,lorentz_comm B A,lorentz_comm C A]

theorem lorentz_smul_right (r : ℝ) (A B : ℝ × ℂ) :
    lorentz A (r • B) = r * lorentz A B := by
  rw [lorentz_comm,lorentz_smul_left,lorentz_comm B A]

/-- Affine extensions lift to a linear combination with a nonpositive first coefficient. -/
theorem extension_coefficients (a b c : Disk) (hab : a ≠ b) (hc : between a b c) :
    ∃ l m : ℝ, l ≤ 0 ∧ lift c = l • lift a + m • lift b := by
  have habv : a.val ≠ b.val := fun he ↦ hab (Subtype.ext he)
  rcases hc.right_mem_image_Ici_of_left_ne habv with ⟨r,hr,he⟩
  let l := (1-r)*sigma a/sigma c
  let m := r*sigma b/sigma c
  have hsc := sigma_pos c
  refine ⟨l,m,div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sigma_pos a).le) hsc.le, ?_⟩
  apply Prod.ext
  · simp only [lift,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    dsimp only [l,m]
    field_simp [ne_of_gt (sigma_pos a),ne_of_gt (sigma_pos b),ne_of_gt hsc]
    ring
  · simp only [lift,Prod.snd_add,Prod.smul_snd]
    rw [←he,lineMap_apply_module]
    apply Complex.ext <;>
      simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul] <;>
      dsimp only [l,m] <;>
      field_simp [ne_of_gt (sigma_pos a),ne_of_gt (sigma_pos b),ne_of_gt hsc]

/-- The extension coefficient is uniquely determined by the two adjacent congruences. -/
theorem coefficients_unique (R S l m l' m' : ℝ) (hR : 1 < R) (hl : l ≤ 0) (hl' : l' ≤ 0)
    (h1 : l^2 + 2*l*m*R + m^2 = 1) (h2 : l'^2 + 2*l'*m'*R + m'^2 = 1)
    (h3 : l*R+m = S) (h4 : l'*R+m' = S) : l = l' ∧ m = m' := by
  have hsquares : (l*R+m)^2 = (l'*R+m')^2 := by rw [h3,h4]
  have he : (l^2-l'^2)*(R^2-1) = 0 := by nlinarith [h1,h2,hsquares]
  have hs : l^2 = l'^2 := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_right (by nlinarith))
  have hlp : l = l' := by nlinarith
  exact ⟨hlp,by rw [hlp] at h3; linarith⟩

/-- All hypotheses of the Tarski five-segment axiom imply its final congruence. -/
theorem five_segment (a b c d a' b' c' d' : Disk) (hab : a ≠ b)
    (hc : between a b c) (hc' : between a' b' c')
    (h1 : congruent a b a' b') (h2 : congruent b c b' c')
    (h3 : congruent a d a' d') (h4 : congruent b d b' d') : congruent c d c' d' := by
  have hab' : a' ≠ b' := by
    intro he
    have hz : coshDist a b = 1 := h1.trans (by rw [he,coshDist_self])
    exact hab ((coshDist_eq_one a b).mp hz)
  rcases extension_coefficients a b c hab hc with ⟨l,m,hl,he⟩
  rcases extension_coefficients a' b' c' hab' hc' with ⟨l',m',hl',he'⟩
  have hR : 1 < coshDist a b := lt_of_le_of_ne (one_le_coshDist a b)
    (fun hz ↦ hab ((coshDist_eq_one a b).mp hz.symm))
  have hunit := lift_lorentz_self c
  have hunit' := lift_lorentz_self c'
  rw [he] at hunit
  rw [he'] at hunit'
  simp only [lorentz_add_left,lorentz_smul_left,lorentz_add_right,lorentz_smul_right,
    lift_lorentz,coshDist_self,coshDist_comm b a,coshDist_comm b' a'] at hunit hunit'
  have hbc : l*coshDist a b+m = coshDist b c := by
    rw [←lift_lorentz b c,he,lorentz_add_right,lorentz_smul_right,lorentz_smul_right,
      lift_lorentz,lift_lorentz_self,coshDist_comm b a]
    ring
  have hbc' : l'*coshDist a b+m' = coshDist b c := by
    rw [h1,h2,←lift_lorentz b' c',he',lorentz_add_right,lorentz_smul_right,
      lorentz_smul_right,lift_lorentz,lift_lorentz_self,coshDist_comm b' a']
    ring
  rw [←h1] at hunit'
  rcases coefficients_unique (coshDist a b) (coshDist b c) l m l' m' hR hl hl'
    (by nlinarith [hunit]) (by nlinarith [hunit']) hbc hbc' with ⟨hlm,hmm⟩
  change coshDist c d = coshDist c' d'
  rw [←lift_lorentz,←lift_lorentz,he,he',lorentz_add_left,lorentz_add_left,
    lorentz_smul_left,lorentz_smul_left,lorentz_smul_left,lorentz_smul_left,
    lift_lorentz,lift_lorentz,lift_lorentz,lift_lorentz,hlm,hmm,h3,h4]

end
end ClassicalTheorems.Progress.Parallel.Klein

#check_upstream ClassicalTheorems.Progress.Parallel.Klein.five_segment

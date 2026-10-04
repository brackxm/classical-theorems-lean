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
import ClassicalTheorems.Progress.ParallelKleinSegment

/-! Completion of the Klein disk model and parallel-postulate independence. -/

namespace ClassicalTheorems.Progress.Parallel.Klein

open Set
noncomputable section

/-- Construct a segment of prescribed hyperbolic cosine on the ray away from `q`. -/
theorem segment_construction_ne (a q : Disk) (haq : a ≠ q) (S : ℝ) (hS : 1 ≤ S) :
    ∃ x : Disk, between q a x ∧ coshDist a x = S := by
  let R := coshDist a q
  have hR : 1 < R := lt_of_le_of_ne (one_le_coshDist a q)
    (fun hz ↦ haq ((coshDist_eq_one a q).mp hz.symm))
  have hden : 0 < R^2-1 := by nlinarith
  let u := Real.sqrt ((S^2-1)/(R^2-1))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2*(R^2-1) = S^2-1 := by
    dsimp only [u]
    rw [Real.sq_sqrt (div_nonneg (by nlinarith) hden.le),div_mul_cancel₀ _ (ne_of_gt hden)]
  let k := S+u*R
  have hk : 0 < k := by dsimp only [k]; nlinarith
  let C : ℝ × ℂ := k • lift a + (-u) • lift q
  have hCunit : lorentz C C = 1 := by
    change lorentz (k • lift a + (-u) • lift q) (k • lift a + (-u) • lift q) = 1
    simp only [lorentz_add_left,lorentz_smul_left,lorentz_add_right,lorentz_smul_right,
      lift_lorentz,coshDist_self,coshDist_comm q a,mul_one]
    change k*(k+(-u)*R)+(-u)*(k*R+(-u)) = 1
    dsimp only [k]
    nlinarith [hu2]
  have hAC : lorentz (lift a) C = S := by
    change lorentz (lift a) (k • lift a+(-u) • lift q) = S
    rw [lorentz_add_right,lorentz_smul_right,lorentz_smul_right,lift_lorentz_self,lift_lorentz]
    dsimp only [k,R]
    ring
  have hCt : 0 < C.1 := lorentz_time_pos (lift a) C (lift_lorentz_self a)
    hCunit (lift_time_pos a) (by rw [hAC]; linarith)
  let x := ofLorentz C hCunit hCt
  have hx : lift x = C := lift_ofLorentz C hCunit hCt
  have hd : 0 < k*(lift a).1 := mul_pos hk (lift_time_pos a)
  have htime : C.1 = k*(lift a).1-u*(lift q).1 := by
    simp only [C,Prod.fst_add,Prod.smul_fst,smul_eq_mul]
    ring
  let t := C.1/(k*(lift a).1)
  have ht0 : 0 ≤ t := div_nonneg hCt.le hd.le
  have ht1 : t ≤ 1 := by
    apply (div_le_one hd).mpr
    have := mul_nonneg hu (lift_time_pos q).le
    linarith [htime]
  have hspace : C.1 • x.val = k • ((lift a).1 • a.val) + (-u) • ((lift q).1 • q.val) := by
    calc C.1 • x.val = (lift x).1 • x.val := by rw [hx]
         _ = (lift x).2 := rfl
         _ = C.2 := by rw [hx]
         _ = k • ((lift a).1 • a.val) + (-u) • ((lift q).1 • q.val) := rfl
  have he : a.val = (1-t) • q.val+t • x.val := by
    apply smul_right_injective ℂ (ne_of_gt hd)
    change (k*(lift a).1) • a.val = (k*(lift a).1) • ((1-t) • q.val+t • x.val)
    rw [smul_add,smul_smul,smul_smul]
    have ht : k*(lift a).1*t = C.1 := by
      dsimp only [t]
      field_simp [ne_of_gt hk,ne_of_gt (lift_time_pos a)]
    have ht' : k*(lift a).1*(1-t) = u*(lift q).1 := by nlinarith [htime,ht]
    rw [ht,ht',hspace]
    module
  refine ⟨x,(Parallel.between_iff _ _ _).mpr ⟨t,ht0,ht1,he⟩,?_⟩
  rw [←lift_lorentz,hx,hAC]

/-- Segment construction, including the coincident ray-endpoint case. -/
theorem segment_construction (a b c q : Disk) :
    ∃ x : Disk, between q a x ∧ congruent a x b c := by
  by_cases haq : a = q
  · have he : origin ≠ east := by
      intro h
      have he := congrArg (fun z : Disk ↦ z.val.re) h
      norm_num [origin,east] at he
    obtain ⟨r,har⟩ : ∃ r : Disk, a ≠ r := by
      by_cases ha : a = origin
      · exact ⟨east,by simpa [ha] using he⟩
      · exact ⟨origin,ha⟩
    rcases segment_construction_ne a r har (coshDist b c) (one_le_coshDist b c)
      with ⟨x,hx,hcosh⟩
    exact ⟨x,by rw [←haq]; exact wbtw_self_left _ _ _,hcosh⟩
  · exact segment_construction_ne a q haq (coshDist b c) (one_le_coshDist b c)

/-- All neutral-plane axioms hold for the Klein disk with hyperbolic congruence. -/
def hyperbolicPlane : Statements.Geometry.NeutralPlane where
  Point := Disk
  between := between
  congruent := congruent
  congruence_reversal := congruence_reversal
  congruence_transitivity := congruence_transitivity
  congruence_identity := congruence_identity
  segment_construction := segment_construction
  five_segment := five_segment
  betweenness_identity := betweenness_identity
  inner_pasch := inner_pasch
  lower_dimension := lower_dimension
  upper_dimension := upper_dimension
  continuity := continuity

theorem hyperbolic_model : ∃ plane : Statements.Geometry.NeutralPlane,
    ¬plane.ParallelPostulate := ⟨hyperbolicPlane,not_euclidean_axiom⟩

end
end ClassicalTheorems.Progress.Parallel.Klein

namespace ClassicalTheorems.Progress.Parallel

theorem parallel_postulate_independence :
    ∃ euclidean hyperbolic : Statements.Geometry.NeutralPlane,
      euclidean.ParallelPostulate ∧ ¬hyperbolic.ParallelPostulate := by
  exact ⟨euclideanPlane,Klein.hyperbolicPlane,euclidean_axiom,Klein.not_euclidean_axiom⟩

end ClassicalTheorems.Progress.Parallel

#check_upstream ClassicalTheorems.Progress.Parallel.Klein.segment_construction
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.hyperbolic_model
#check_upstream ClassicalTheorems.Progress.Parallel.parallel_postulate_independence

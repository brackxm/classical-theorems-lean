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
import ClassicalTheorems.Progress.ParallelEuclidean

/-! Affine and metric ingredients of the Klein disk model for parallel-postulate independence.
The complete neutral-plane model is assembled in `ParallelKleinModel`. -/

namespace ClassicalTheorems.Progress.Parallel.Klein

open Set

noncomputable section

/-- Points in the open unit disk, expressed using squared norm. -/
def Disk := {z : ℂ // Complex.normSq z < 1}

def between (a b c : Disk) : Prop := Wbtw ℝ a.val b.val c.val

/-- The open disk is convex; hence affine Pasch witnesses remain in the model. -/
theorem norm_lt_one (a : Disk) : ‖a.val‖ < 1 := by
  have h := a.property
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg a.val]

theorem mem_disk_of_between (a b : Disk) (x : ℂ) (hx : Wbtw ℝ a.val x b.val) :
    Complex.normSq x < 1 := by
  have hx' : ‖x‖ < 1 := by
    have hb : x ∈ Metric.ball (0 : ℂ) 1 :=
      (convex_ball (0 : ℂ) 1).segment_subset (by simpa using norm_lt_one a)
        (by simpa using norm_lt_one b) hx.mem_segment
    simpa using hb
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg x]

theorem betweenness_identity (a b : Disk) (h : between a b a) : a = b := by
  exact Subtype.ext ((wbtw_self_iff ℝ).mp h).symm

theorem inner_pasch (a b c p q : Disk) (hp : between a p c) (hq : between b q c) :
    ∃ x : Disk, between p x b ∧ between q x a := by
  rcases Parallel.inner_pasch a.val b.val c.val p.val q.val hp hq with ⟨x, hx, hx'⟩
  exact ⟨⟨x, mem_disk_of_between p b x hx⟩, hx, hx'⟩

theorem continuity (X Y : Set Disk)
    (h : ∃ a, ∀ x ∈ X, ∀ y ∈ Y, between a x y) :
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, between x b y := by
  classical
  rcases h with ⟨a, ha⟩
  rcases X.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · exact ⟨a, by simp⟩
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y0, hy0⟩
  · exact ⟨a, by simp⟩
  have h' : ∃ z : ℂ, ∀ x ∈ Subtype.val '' X, ∀ y ∈ Subtype.val '' Y,
      Wbtw ℝ z x y := by
    refine ⟨a.val, ?_⟩
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact ha x hx y hy
  rcases Parallel.continuity _ _ h' with ⟨z, hz⟩
  have hz' := hz x0.val ⟨x0,hx0,rfl⟩ y0.val ⟨y0,hy0,rfl⟩
  exact ⟨⟨z,mem_disk_of_between x0 y0 z hz'⟩,
    fun x hx y hy ↦ hz x.val ⟨x,hx,rfl⟩ y.val ⟨y,hy,rfl⟩⟩

def origin : Disk := ⟨0, by norm_num [Complex.normSq_apply]⟩
def east : Disk := ⟨⟨1/2,0⟩, by norm_num [Complex.normSq_apply]⟩
def north : Disk := ⟨⟨0,1/2⟩, by norm_num [Complex.normSq_apply]⟩
def diagonal : Disk := ⟨⟨1/4,1/4⟩, by norm_num [Complex.normSq_apply]⟩
def tip : Disk := ⟨⟨3/5,3/5⟩, by norm_num [Complex.normSq_apply]⟩

theorem lower_dimension : ∃ a b c : Disk,
    ¬between a b c ∧ ¬between b c a ∧ ¬between c a b := by
  refine ⟨origin,east,north,?_,?_,?_⟩
  · intro h
    rcases (Parallel.between_iff _ _ _).mp h with ⟨t,ht0,ht1,he⟩
    have hr := congrArg Complex.re he
    norm_num [origin,east,north,Complex.smul_re,smul_eq_mul] at hr
  · intro h
    rcases (Parallel.between_iff _ _ _).mp h with ⟨t,ht0,ht1,he⟩
    have hi := congrArg Complex.im he
    norm_num [origin,east,north,Complex.smul_im,smul_eq_mul] at hi
  · intro h
    rcases (Parallel.between_iff _ _ _).mp h with ⟨t,ht0,ht1,he⟩
    have hr := congrArg Complex.re he
    have hi := congrArg Complex.im he
    norm_num [origin,east,north,Complex.smul_re,Complex.smul_im,smul_eq_mul] at hr hi
    linarith

/-- An explicit failure of Tarski's Euclidean axiom inside the Klein disk.
The congruence axioms are proved in the metric, five-segment and model modules. -/
theorem not_euclidean_axiom : ¬ (∀ a b c d t : Disk,
    between a d t → between b d c → a ≠ d →
    ∃ x y, between a b x ∧ between a c y ∧ between x t y) := by
  intro h
  have h1 : between origin diagonal tip :=
    (Parallel.between_iff _ _ _).mpr ⟨5/12,by norm_num,by norm_num,by
      apply Complex.ext <;> norm_num [origin,diagonal,tip,Complex.smul_re,Complex.smul_im]⟩
  have h2 : between east diagonal north :=
    (Parallel.between_iff _ _ _).mpr ⟨1/2,by norm_num,by norm_num,by
      apply Complex.ext <;> norm_num [east,diagonal,north,Complex.smul_re,Complex.smul_im]⟩
  have hne : origin ≠ diagonal := by
    intro he
    have := congrArg (fun z : Disk ↦ z.val.re) he
    norm_num [origin,diagonal] at this
  rcases h origin east north diagonal tip h1 h2 hne with ⟨x,y,hx,hy,ht⟩
  rcases (Parallel.between_iff _ _ _).mp hx with ⟨r,hr0,hr1,hex⟩
  rcases (Parallel.between_iff _ _ _).mp hy with ⟨s,hs0,hs1,hey⟩
  have hre := congrArg Complex.re hex
  have him := congrArg Complex.im hex
  have hre' := congrArg Complex.re hey
  have him' := congrArg Complex.im hey
  norm_num [origin,east,north,Complex.smul_re,Complex.smul_im,smul_eq_mul] at hre him hre' him'
  have hx0 : x.val.im = 0 := him.resolve_left (by intro hz; simp [hz] at hre)
  have hy0 : y.val.re = 0 := hre'.resolve_left (by intro hz; simp [hz] at him')
  have hx1 : x.val.re < 1 := by
    have hxnorm := x.property
    simp [Complex.normSq_apply,hx0] at hxnorm
    nlinarith
  have hy1 : y.val.im < 1 := by
    have hynorm := y.property
    simp [Complex.normSq_apply,hy0] at hynorm
    nlinarith
  rcases (Parallel.between_iff _ _ _).mp ht with ⟨u,hu0,hu1,het⟩
  have hrt := congrArg Complex.re het
  have hit := congrArg Complex.im het
  norm_num [tip,Complex.smul_re,Complex.smul_im,smul_eq_mul,hx0,hy0] at hrt hit
  have hupper := add_le_add (mul_le_mul_of_nonneg_left hx1.le (sub_nonneg.mpr hu1))
    (mul_le_mul_of_nonneg_left hy1.le hu0)
  nlinarith

end

end ClassicalTheorems.Progress.Parallel.Klein

#check_upstream ClassicalTheorems.Progress.Parallel.Klein.inner_pasch
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.continuity
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.lower_dimension
#check_upstream ClassicalTheorems.Progress.Parallel.Klein.not_euclidean_axiom

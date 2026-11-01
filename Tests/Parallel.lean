/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Parallel
import Mathlib.Tactic.NormNum

/-!
# Concrete Euclidean and Klein-model witnesses

Use a = (0, 0), b = (1/3, 0), c = (0, 2/3), d = (4/21, 2/7), and
t = (1/2, 3/4). All are strictly inside the Klein disk. Tarski's Euclidean
axiom has explicit plane witnesses (7/8, 0) and (0, 7/4), but no disk witnesses:
any admissible pair of axis intercepts inside the disk has its entire segment
in x + y < 1, while t has x + y = 5/4.

Equal Euclidean chords from 0 to 1/3 and from 1/3 to 2/3 on the real axis
also have different hyperbolic cosines. This checks the model's congruence
interpretation as well as its restricted point domain.
-/

noncomputable section
open Set ClassicalTheorems.Progress.Parallel

namespace ClassicalTheoremsTest.Parallel

private def a : Klein.Disk := ⟨0, by norm_num [Complex.normSq_apply]⟩
private def b : Klein.Disk := ⟨⟨1/3, 0⟩, by norm_num [Complex.normSq_apply]⟩
private def c : Klein.Disk := ⟨⟨0, 2/3⟩, by norm_num [Complex.normSq_apply]⟩
private def d : Klein.Disk := ⟨⟨4/21, 2/7⟩, by norm_num [Complex.normSq_apply]⟩
private def tip : Klein.Disk := ⟨⟨1/2, 3/4⟩, by norm_num [Complex.normSq_apply]⟩
private def radial : Klein.Disk := ⟨⟨2/3, 0⟩, by norm_num [Complex.normSq_apply]⟩
private abbrev x : ℂ := ⟨7/8, 0⟩
private abbrev y : ℂ := ⟨0, 7/4⟩

/-- The counterexample satisfies all three actual model hypotheses of Tarski's axiom. -/
theorem tarski_hypotheses :
    Klein.hyperbolicPlane.between a d tip ∧
    Klein.hyperbolicPlane.between b d c ∧ a ≠ d := by
  refine ⟨?_, ?_, ?_⟩
  · apply (between_iff _ _ _).mpr
    refine ⟨8/21, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [a, d, tip, Complex.smul_re, Complex.smul_im]
  · apply (between_iff _ _ _).mpr
    refine ⟨3/7, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [b, c, d, Complex.smul_re, Complex.smul_im]
  · intro h
    have hr := congrArg (fun z : Klein.Disk => z.val.re) h
    norm_num [a, d] at hr

/-- The same configuration has these explicit witnesses in the full Euclidean plane. -/
theorem euclidean_witnesses :
    euclideanPlane.between a.val b.val x ∧
    euclideanPlane.between a.val c.val y ∧
    euclideanPlane.between x tip.val y := by
  refine ⟨?_, ?_, ?_⟩
  · apply (between_iff _ _ _).mpr
    refine ⟨8/21, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [a, b, x, Complex.smul_re, Complex.smul_im]
  · apply (between_iff _ _ _).mpr
    refine ⟨8/21, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [a, c, y, Complex.smul_re, Complex.smul_im]
  · apply (between_iff _ _ _).mpr
    refine ⟨3/7, by norm_num, by norm_num, ?_⟩
    apply Complex.ext <;> norm_num [tip, x, y, Complex.smul_re, Complex.smul_im]

/-- The second Euclidean witness is unavailable as a disk point. -/
theorem euclidean_witness_outside_disk : ¬Complex.normSq y < 1 := by
  norm_num [y, Complex.normSq_apply]

private theorem x_axis_of_between (u : Klein.Disk)
    (h : Klein.hyperbolicPlane.between a b u) : u.val.im = 0 := by
  rcases (between_iff _ _ _).mp h with ⟨r, _, _, he⟩
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  norm_num [a, b, Complex.smul_re, Complex.smul_im, smul_eq_mul] at hr hi
  have hne : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    norm_num at hr
  exact hi.resolve_left hne

private theorem y_axis_of_between (v : Klein.Disk)
    (h : Klein.hyperbolicPlane.between a c v) : v.val.re = 0 := by
  rcases (between_iff _ _ _).mp h with ⟨r, _, _, he⟩
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  norm_num [a, c, Complex.smul_re, Complex.smul_im, smul_eq_mul] at hr hi
  have hne : r ≠ 0 := by
    intro hz
    rw [hz] at hi
    norm_num at hi
  exact hr.resolve_left hne

/-- No alternative pair of disk witnesses can solve the same Euclidean-axiom instance. -/
theorem no_disk_witnesses :
    ¬∃ u v : Klein.Disk, Klein.hyperbolicPlane.between a b u ∧
      Klein.hyperbolicPlane.between a c v ∧ Klein.hyperbolicPlane.between u tip v := by
  rintro ⟨u, v, hu, hv, ht⟩
  have hu0 := x_axis_of_between u hu
  have hv0 := y_axis_of_between v hv
  let cut : ℂ →L[ℝ] ℝ := Complex.reCLM + Complex.imCLM
  have hub : cut u.val < 1 := by
    have hn := u.property
    norm_num [Complex.normSq_apply, hu0] at hn
    change u.val.re + u.val.im < 1
    rw [hu0, add_zero]
    nlinarith [sq_nonneg (u.val.re - 1)]
  have hvb : cut v.val < 1 := by
    have hn := v.property
    norm_num [Complex.normSq_apply, hv0] at hn
    change v.val.re + v.val.im < 1
    rw [hv0, zero_add]
    nlinarith [sq_nonneg (v.val.im - 1)]
  have hconv : Convex ℝ {z : ℂ | cut z < 1} :=
    convex_halfSpace_lt (LinearMap.isLinear cut.toLinearMap) 1
  have hsegment : tip.val ∈ segment ℝ u.val v.val :=
    (show Wbtw ℝ u.val tip.val v.val from ht).mem_segment
  have htip : cut tip.val < 1 := hconv.segment_subset hub hvb hsegment
  norm_num [cut, tip] at htip

/-- The assembled neutral-plane records give opposite parallel-postulate verdicts. -/
theorem model_verdicts : euclideanPlane.ParallelPostulate ∧
    ¬Klein.hyperbolicPlane.ParallelPostulate := by
  refine ⟨euclidean_axiom, ?_⟩
  intro h
  exact no_disk_witnesses
    (h a b c d tip tarski_hypotheses.1 tarski_hypotheses.2.1 tarski_hypotheses.2.2)

private theorem squared_hyperbolic_cosines :
    Klein.coshDist a b ^ 2 = 9/8 ∧ Klein.coshDist b radial ^ 2 = 49/40 := by
  constructor
  · rw [Klein.coshDist, div_pow, mul_pow, Klein.sigma_sq, Klein.sigma_sq]
    norm_num [a, b]
  · rw [Klein.coshDist, div_pow, mul_pow, Klein.sigma_sq, Klein.sigma_sq]
    norm_num [b, radial]

/-- Equal Euclidean chords are unequal in the Klein model's actual congruence relation. -/
theorem congruence_distinguishes_models :
    euclideanPlane.congruent a.val b.val b.val radial.val ∧
    ¬Klein.hyperbolicPlane.congruent a b b radial := by
  constructor
  · change dist a.val b.val = dist b.val radial.val
    rw [dist_eq_norm, dist_eq_norm]
    norm_num [a, b, radial, Complex.norm_def, Complex.normSq_apply]
  · intro h
    change Klein.coshDist a b = Klein.coshDist b radial at h
    have hs := congrArg (fun r : ℝ => r ^ 2) h
    rw [squared_hyperbolic_cosines.1, squared_hyperbolic_cosines.2] at hs
    norm_num at hs

#check_upstream tarski_hypotheses
#check_upstream euclidean_witnesses
#check_upstream euclidean_witness_outside_disk
#check_upstream no_disk_witnesses
#check_upstream model_verdicts
#check_upstream congruence_distinguishes_models

end ClassicalTheoremsTest.Parallel

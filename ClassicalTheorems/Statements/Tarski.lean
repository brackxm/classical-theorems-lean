/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Set.Basic

/-! Tarski neutral-plane axioms, with the Euclidean axiom kept separate. -/

namespace ClassicalTheorems.Statements.Geometry

structure NeutralPlane where
  Point : Type
  between : Point → Point → Point → Prop
  congruent : Point → Point → Point → Point → Prop
  congruence_reversal : ∀ a b, congruent a b b a
  congruence_transitivity : ∀ a b p q r s,
    congruent a b p q → congruent a b r s → congruent p q r s
  congruence_identity : ∀ a b c, congruent a b c c → a = b
  segment_construction : ∀ a b c q,
    ∃ x, between q a x ∧ congruent a x b c
  five_segment : ∀ a b c d a' b' c' d',
    a ≠ b → between a b c → between a' b' c' →
    congruent a b a' b' → congruent b c b' c' →
    congruent a d a' d' → congruent b d b' d' → congruent c d c' d'
  betweenness_identity : ∀ a b, between a b a → a = b
  inner_pasch : ∀ a b c p q,
    between a p c → between b q c → ∃ x, between p x b ∧ between q x a
  lower_dimension : ∃ a b c,
    ¬between a b c ∧ ¬between b c a ∧ ¬between c a b
  upper_dimension : ∀ a b c p q, p ≠ q →
    congruent a p a q → congruent b p b q → congruent c p c q →
    between a b c ∨ between b c a ∨ between c a b
  continuity : ∀ X Y : Set Point,
    (∃ a, ∀ x ∈ X, ∀ y ∈ Y, between a x y) →
    ∃ b, ∀ x ∈ X, ∀ y ∈ Y, between x b y

/-- Tarski's Euclidean axiom, equivalent to the parallel postulate in neutral geometry. -/
def NeutralPlane.ParallelPostulate (plane : NeutralPlane) : Prop :=
  ∀ a b c d t : plane.Point,
    plane.between a d t → plane.between b d c → a ≠ d →
    ∃ x y, plane.between a b x ∧ plane.between a c y ∧ plane.between x t y

end ClassicalTheorems.Statements.Geometry

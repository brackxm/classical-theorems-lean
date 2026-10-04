/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Statements.Arithmetic
import ClassicalTheorems.Progress.FoundationEffectiveConsequences

/-! A Foundation proof language with exactly the project's four function
symbols. Its sole relation is equality. Successor remains a primitive symbol,
so this bridge does not assume arithmetic identities in arbitrary structures. -/

noncomputable section
open Classical
open ClassicalTheorems.Statements.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
namespace ClassicalTheorems.Progress.Arithmetic

def proofLanguage : FFL.FirstOrder.Language where
  Func := language.Functions
  Rel n := Fin (if n = 2 then 1 else 0)

instance : proofLanguage.Encodable where
  func k := inferInstanceAs (Encodable
    (Fin (if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 else 0)))
  rel k := inferInstanceAs (Encodable (Fin (if k = 2 then 1 else 0)))

instance : proofLanguage.DecidableEq where
  func k := inferInstanceAs (DecidableEq
    (Fin (if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 else 0)))
  rel k := inferInstanceAs (DecidableEq (Fin (if k = 2 then 1 else 0)))

def proofEq : proofLanguage.Rel 2 := ⟨0, by decide⟩

instance : proofLanguage.Eq := ⟨proofEq⟩

instance : proofLanguage.Primcodable where
  func := by
    have h : Primrec (fun p : ℕ × ℕ =>
        if p.2 < (if p.1 = 0 then 1 else if p.1 = 1 then 1 else if p.1 = 2 then 2 else 0)
        then p.2 + 1 else 0) := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    change (if e < _ then e + 1 else 0) =
      Encodable.encode (Encodable.decode e : Option (Fin _))
    simp only [Encodable.decode, Encodable.decodeSubtype, Option.bind_some]
    split_ifs <;> rfl
  rel := by
    have h : Primrec (fun p : ℕ × ℕ => if p.2 < (if p.1 = 2 then 1 else 0)
        then p.2 + 1 else 0) := by primrec
    apply h.of_eq
    rintro ⟨k, e⟩
    change (if e < _ then e + 1 else 0) =
      Encodable.encode (Encodable.decode e : Option (Fin _))
    simp only [Encodable.decode, Encodable.decodeSubtype, Option.bind_some]
    split_ifs <;> rfl

instance : proofLanguage.LORDefinable where
  func := .mkSigma “k c. ((k = 0 ∨ k = 1) ∧ c = 0) ∨ (k = 2 ∧ c < 2)” (by simp)
  rel := .mkSigma “k c. k = 2 ∧ c = 0” (by simp)
  func_iff := by
    intro k c
    change (∃ f : Fin (if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 else 0),
      (f : ℕ) = c) ↔ ((k = 0 ∨ k = 1) ∧ c = 0) ∨ (k = 2 ∧ c < 2)
    constructor
    · rintro ⟨f, hf⟩
      have hc : c < (if k = 0 then 1 else if k = 1 then 1 else if k = 2 then 2 else 0) :=
        hf ▸ f.isLt
      split_ifs at hc <;> omega
    · intro h
      refine ⟨⟨c, ?_⟩, rfl⟩
      split_ifs <;> omega
  rel_iff := by
    intro k c
    change (∃ f : Fin (if k = 2 then 1 else 0), (f : ℕ) = c) ↔ k = 2 ∧ c = 0
    constructor
    · rintro ⟨f, rfl⟩
      have h := f.isLt
      split_ifs at h <;> omega
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨0, by decide⟩, rfl⟩

theorem proof_function_bounds (f : Σ n, proofLanguage.Func n) :
    f.1 < 3 ∧ f.2.val < 2 := by
  obtain ⟨n, f⟩ := f
  change n < 3 ∧ f.val < 2
  have h := f.isLt
  change f.val < (if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 2 else 0) at h
  by_cases h0 : n = 0
  · simp only [h0, ite_eq_left] at h
    omega
  by_cases h1 : n = 1
  · simp only [ite_eq_right h0, ite_eq_left h1] at h
    omega
  by_cases h2 : n = 2
  · simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_left h2] at h
    omega
  simp only [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2] at h
  omega

instance : Finite (Σ n, proofLanguage.Func n) := by
  let embed (f : Σ n, proofLanguage.Func n) : Fin 3 × Fin 2 :=
    (⟨f.1, (proof_function_bounds f).1⟩, ⟨f.2.val, (proof_function_bounds f).2⟩)
  apply Finite.of_injective embed
  rintro ⟨n, f⟩ ⟨m, g⟩ h
  have hnm : n = m := congrArg (fun x : Fin 3 × Fin 2 => x.1.val) h
  subst m
  have hfg : f = g := Fin.ext (congrArg (fun x : Fin 3 × Fin 2 => x.2.val) h)
  subst g
  rfl

instance : Finite (Σ n, proofLanguage.Rel n) := by
  have hrel (r : Σ n, proofLanguage.Rel n) : r = ⟨2, proofEq⟩ := by
    obtain ⟨n, r⟩ := r
    have hn : n = 2 := by
      have h := r.isLt
      change r.val < (if n = 2 then 1 else 0) at h
      split_ifs at h <;> omega
    subst n
    have hr : r = proofEq := by
      apply Fin.ext
      have h := r.isLt
      change r.val < 1 at h
      change r.val = 0
      omega
    subst r
    rfl
  apply Finite.of_injective (fun _ : Σ n, proofLanguage.Rel n => ())
  intro r s _
  exact (hrel r).trans (hrel s).symm

instance : proofLanguage.Finite where
  func := Fintype.ofFinite _
  rel := Fintype.ofFinite _

theorem proof_equality_axioms_finite : Set.Finite (𝗘𝗤 proofLanguage) :=
  FFL.FirstOrder.Theory.EqAxiom.finite

theorem proofLanguage_provability_re (theory : FFL.FirstOrder.Theory proofLanguage) [theory.RE] :
    REPred (fun φ : FFL.FirstOrder.Sentence proofLanguage => theory ⊢ φ) :=
  foundation_provability_re theory

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.proof_equality_axioms_finite
#check_upstream ClassicalTheorems.Progress.Arithmetic.proofLanguage_provability_re

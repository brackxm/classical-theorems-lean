/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import Mathlib.Computability.RE

/-! A concrete pair of disjoint recursively enumerable predicates with no
computable separator. This is the computational obstruction in a possible
Robinson-Q essential-incompleteness proof. -/

noncomputable section
open Classical Denumerable
open Nat.Partrec (Code)
open Nat.Partrec.Code
namespace ClassicalTheorems.Progress.Arithmetic

/-- The program numbered n, run on its own number, returns the given output. -/
def diagonalOutput (output n : ℕ) : Prop := output ∈ eval (ofNat Code n) n

theorem diagonal_output_disjoint (n : ℕ) : ¬ (diagonalOutput 0 n ∧ diagonalOutput 1 n) := by
  rintro ⟨h0, h1⟩
  have h : (0 : ℕ) = 1 := Part.mem_unique h0 h1
  exact Nat.zero_ne_one h

theorem diagonal_output_re (output : ℕ) : REPred (diagonalOutput output) := by
  let f (n : ℕ) : Part Unit := (eval (ofNat Code n) n).bind
    (fun x => if x = output then Part.some () else Part.none)
  have htest : Computable (fun p : ℕ × ℕ => decide (p.2 = output)) :=
    (Primrec.eq.comp Primrec.snd (Primrec.const output)).decide.to_comp
  have hfilter : Partrec (fun p : ℕ × ℕ =>
      if p.2 = output then Part.some () else Part.none) := by
    simpa only [Bool.cond_decide] using
      (Partrec.cond htest (Decidable.Partrec.const' (Part.some ())) Partrec.none)
  have hf : Partrec f :=
    (eval_part.comp (Computable.ofNat Code) Computable.id).bind hfilter.to₂
  apply hf.dom_re.of_eq
  intro n
  simp only [f, diagonalOutput, Part.dom_iff_mem, Part.mem_bind_iff]
  constructor
  · rintro ⟨u, x, hx, hu⟩
    by_cases he : x = output
    · exact he ▸ hx
    · simp [he] at hu
  · intro hx
    exact ⟨(), output, hx, by simp⟩

/-- No computable predicate includes every self-zero program while excluding
every self-one program: its opposite answer would itself be a counterexample. -/
theorem diagonal_output_inseparable (p : ℕ → Prop) (hp : ComputablePred p)
    (hzero : ∀ n, diagonalOutput 0 n → p n)
    (hone : ∀ n, diagonalOutput 1 n → ¬ p n) : False := by
  let f (n : ℕ) : ℕ := if p n then 1 else 0
  have hf : Computable f := hp.ite (Computable.const 1) (Computable.const 0)
  obtain ⟨c, hc⟩ := exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  let n := Encodable.encode c
  by_cases h : p n
  · have hout : diagonalOutput 1 n := by
      simp [diagonalOutput, n, hc, f, h]
    exact hone n hout h
  · have hout : diagonalOutput 0 n := by
      simp [diagonalOutput, n, hc, f, h]
    exact h (hzero n hout)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.diagonal_output_re
#check_upstream ClassicalTheorems.Progress.Arithmetic.diagonal_output_inseparable

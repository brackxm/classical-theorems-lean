/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticModels
import Mathlib.Tactic.FinCases

/-! Arithmetic of standard numerals in every model of the exact Robinson
axioms. Finite bounds can be unfolded without assuming induction in the model. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

variable {M : Type*} [language.Structure M]

def modelZero : M := Structure.funMap (L := language) ⟨0, by decide⟩ Fin.elim0
def modelSucc (x : M) : M := Structure.funMap (L := language) ⟨0, by decide⟩ ![x]
def modelAdd (x y : M) : M := Structure.funMap (L := language) ⟨0, by decide⟩ ![x, y]
def modelMul (x y : M) : M := Structure.funMap (L := language) ⟨1, by decide⟩ ![x, y]

theorem realize_model_zero (env : ℕ → M) : zero.realize env = modelZero := by
  simp only [zero, Term.realize, modelZero]
  congr 1
  funext i
  exact Fin.elim0 i
theorem realize_model_succ (env : ℕ → M) (t : T) :
    (succ t).realize env = modelSucc (t.realize env) := by
  simp only [succ, Term.realize, modelSucc]
  congr 1
  funext i
  fin_cases i
  rfl
theorem realize_model_add (env : ℕ → M) (t u : T) :
    (add t u).realize env = modelAdd (t.realize env) (u.realize env) := by
  simp only [add, Term.realize, modelAdd]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem realize_model_mul (env : ℕ → M) (t u : T) :
    (mul t u).realize env = modelMul (t.realize env) (u.realize env) := by
  simp only [mul, Term.realize, modelMul]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Standard numerals use only zero and successor of the given structure. -/
def modelNumeral : ℕ → M
  | 0 => modelZero
  | n + 1 => modelSucc (modelNumeral n)

@[simp] theorem model_numeral_zero : modelNumeral (M := M) 0 = modelZero := rfl
@[simp] theorem model_numeral_succ (n : ℕ) :
    modelNumeral (M := M) (n + 1) = modelSucc (modelNumeral n) := rfl

section Models
variable [Nonempty M] [M ⊨ robinson]

theorem robinson_axiom (φ : language.Formula ℕ) (hφ : closeAll φ ∈ robinson)
    (env : ℕ → M) : φ.Realize env :=
  (realize_closeAll φ).mp (Theory.realize_sentence_of_mem robinson hφ) env

theorem model_succ_ne_zero (x : M) : modelSucc x ≠ (modelZero : M) := by
  have h := robinson_axiom ((succ (v 0)).equal zero).not (by simp [robinson]) (fun _ => x)
  simpa only [Formula.realize_not, Formula.realize_equal, realize_model_succ,
    realize_model_zero, realize_v] using h

theorem model_succ_injective : Function.Injective (modelSucc : M → M) := by
  intro x y
  have h := robinson_axiom (((succ (v 0)).equal (succ (v 1))).imp ((v 0).equal (v 1)))
    (by simp [robinson]) (fun i => if i = 0 then x else y)
  simpa [Formula.realize_equal, realize_model_succ] using h

theorem model_predecessor (x : M) (hx : x ≠ (modelZero : M)) :
    ∃ y, x = modelSucc y := by
  have h := robinson_axiom (((v 0).equal zero).not.imp (exV 1 ((v 0).equal (succ (v 1)))))
    (by simp [robinson]) (fun _ => x)
  have h' : x ≠ (modelZero : M) → ∃ y, x = modelSucc y := by
    simpa [Formula.realize_equal, realize_exV, realize_model_succ, realize_model_zero] using h
  exact h' hx

@[simp] theorem model_add_zero (x : M) : modelAdd x modelZero = x := by
  have h := robinson_axiom ((add (v 0) zero).equal (v 0)) (by simp [robinson]) (fun _ => x)
  simpa only [Formula.realize_equal, realize_model_add, realize_model_zero, realize_v] using h

theorem model_add_succ (x y : M) : modelAdd x (modelSucc y) = modelSucc (modelAdd x y) := by
  have h := robinson_axiom ((add (v 0) (succ (v 1))).equal (succ (add (v 0) (v 1))))
    (by simp [robinson]) (fun i => if i = 0 then x else y)
  simpa [Formula.realize_equal, realize_model_add, realize_model_succ] using h

@[simp] theorem model_mul_zero (x : M) : modelMul x modelZero = modelZero := by
  have h := robinson_axiom ((mul (v 0) zero).equal zero) (by simp [robinson]) (fun _ => x)
  simpa only [Formula.realize_equal, realize_model_mul, realize_model_zero, realize_v] using h

theorem model_mul_succ (x y : M) :
    modelMul x (modelSucc y) = modelAdd (modelMul x y) x := by
  have h := robinson_axiom ((mul (v 0) (succ (v 1))).equal (add (mul (v 0) (v 1)) (v 0)))
    (by simp [robinson]) (fun i => if i = 0 then x else y)
  simpa [Formula.realize_equal, realize_model_mul, realize_model_succ, realize_model_add] using h

theorem model_numeral_injective : Function.Injective (modelNumeral : ℕ → M) := by
  intro n
  induction n with
  | zero =>
    intro m h
    cases m with
    | zero => rfl
    | succ m => exact False.elim (model_succ_ne_zero _ h.symm)
  | succ n ih =>
    intro m h
    cases m with
    | zero => exact False.elim (model_succ_ne_zero _ h)
    | succ m => exact congrArg Nat.succ (ih (model_succ_injective h))

theorem model_numeral_add (n m : ℕ) :
    modelAdd (modelNumeral (M := M) n) (modelNumeral m) = modelNumeral (n + m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [model_numeral_succ, model_add_succ, ih, Nat.add_succ, model_numeral_succ]

theorem model_numeral_mul (n m : ℕ) :
    modelMul (modelNumeral (M := M) n) (modelNumeral m) = modelNumeral (n * m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [model_numeral_succ, model_mul_succ, ih, model_numeral_add, Nat.mul_succ]

/-- If a sum is a standard numeral, its right summand is one of finitely many
standard numerals. The orientation follows the Robinson recursion axiom. -/
theorem model_right_summand_bounded (n : ℕ) (x y : M)
    (h : modelAdd y x = modelNumeral n) : ∃ k ≤ n, x = modelNumeral k := by
  induction n generalizing x y with
  | zero =>
    by_cases hx : x = modelZero
    · exact ⟨0, le_rfl, hx⟩
    · obtain ⟨u, rfl⟩ := model_predecessor x hx
      rw [model_add_succ] at h
      exact False.elim (model_succ_ne_zero _ h)
  | succ n ih =>
    by_cases hx : x = modelZero
    · exact ⟨0, Nat.zero_le _, hx⟩
    · obtain ⟨u, rfl⟩ := model_predecessor x hx
      rw [model_add_succ, model_numeral_succ] at h
      obtain ⟨k, hk, rfl⟩ := ih u y (model_succ_injective h)
      exact ⟨k + 1, Nat.succ_le_succ hk, rfl⟩

/-- The arithmetic bound is an existential addition equation, requiring no
order symbols or order axioms beyond the seven original axioms. -/
def modelLE (x y : M) : Prop := ∃ d, modelAdd d x = y
def modelLT (x y : M) : Prop := modelLE (modelSucc x) y

theorem model_le_numeral_iff (x : M) (n : ℕ) :
    modelLE x (modelNumeral n) ↔ ∃ k ≤ n, x = modelNumeral k := by
  constructor
  · rintro ⟨d, hd⟩
    exact model_right_summand_bounded n x d hd
  · rintro ⟨k, hk, rfl⟩
    refine ⟨modelNumeral (n - k), ?_⟩
    rw [model_numeral_add, Nat.sub_add_cancel hk]

theorem model_lt_numeral_iff (x : M) (n : ℕ) :
    modelLT x (modelNumeral n) ↔ ∃ k < n, x = modelNumeral k := by
  rw [modelLT, model_le_numeral_iff]
  constructor
  · rintro ⟨k, hk, he⟩
    cases k with
    | zero => exact False.elim (model_succ_ne_zero _ he)
    | succ k => exact ⟨k, by omega, model_succ_injective he⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k + 1, by omega, rfl⟩

/-- Every element is comparable to any standard numeral in the definable
addition bound, even though no linear order on the whole model is assumed. -/
theorem model_le_total_numeral (x : M) (n : ℕ) :
    modelLE x (modelNumeral n) ∨ modelLE (modelNumeral n) x := by
  induction n generalizing x with
  | zero => exact Or.inr ⟨x, model_add_zero x⟩
  | succ n ih =>
    by_cases hx : x = modelZero
    · subst x
      exact Or.inl ⟨modelNumeral (n + 1), model_add_zero _⟩
    · obtain ⟨y, rfl⟩ := model_predecessor x hx
      rcases ih y with ⟨d, hd⟩ | ⟨d, hd⟩
      · exact Or.inl ⟨d, by rw [model_add_succ, hd]; rfl⟩
      · exact Or.inr ⟨d, by rw [model_numeral_succ, model_add_succ, hd]⟩

end Models
end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_numeral_injective
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_numeral_add
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_numeral_mul
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_le_numeral_iff
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_lt_numeral_iff
#check_upstream ClassicalTheorems.Progress.Arithmetic.model_le_total_numeral

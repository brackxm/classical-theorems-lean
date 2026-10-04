/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonNumerals

/-! Bounded arithmetic formulas in the exact first-order syntax of the optional
Robinson-Q statement. Standard numeral inputs have the same truth value in
every Robinson model as in the standard natural numbers. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

@[simp] theorem model_numeral_nat (n : ℕ) : modelNumeral (M := ℕ) n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.succ (modelNumeral (M := ℕ) n) = Nat.succ n
    rw [ih]

section Models
variable {M : Type*} [language.Structure M] [Nonempty M] [M ⊨ robinson]

theorem model_function_numerals {n : ℕ} (f : language.Functions n) (xs : Fin n → ℕ) :
    Structure.funMap f (fun i => modelNumeral (M := M) (xs i)) =
      modelNumeral (Structure.funMap (M := ℕ) f xs) := by
  cases n with
  | zero =>
    have hf : f = (⟨0, by decide⟩ : language.Functions 0) := by
      apply Fin.ext
      change f.val = 0
      have h := f.isLt
      change f.val < 1 at h
      omega
    subst f
    have hx : (fun i => modelNumeral (M := M) (xs i)) =
        (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
    rw [hx]
    rfl
  | succ n =>
    cases n with
    | zero =>
      have hf : f = (⟨0, by decide⟩ : language.Functions 1) := by
        apply Fin.ext
        change f.val = 0
        have h := f.isLt
        change f.val < 1 at h
        omega
      subst f
      have hx : (fun i => modelNumeral (M := M) (xs i)) = ![modelNumeral (xs 0)] := by
        funext i
        fin_cases i
        rfl
      rw [hx]
      rfl
    | succ n =>
      cases n with
      | zero =>
        have hx : (fun i => modelNumeral (M := M) (xs i)) =
            ![modelNumeral (xs 0), modelNumeral (xs 1)] := by
          funext i
          fin_cases i <;> rfl
        rw [hx]
        have hf : f.val = 0 ∨ f.val = 1 := by have h := f.isLt; change f.val < 2 at h; omega
        rcases hf with hf | hf
        · have hf' : f = (⟨0, by decide⟩ : language.Functions 2) := Fin.ext hf
          subst f
          exact model_numeral_add _ _
        · have hf' : f = (⟨1, by decide⟩ : language.Functions 2) := Fin.ext hf
          subst f
          exact model_numeral_mul _ _
      | succ n =>
        have hz : (if n + 3 = 0 then 1 else if n + 3 = 1 then 1 else
            if n + 3 = 2 then 2 else 0) = 0 := by split_ifs <;> omega
        have h : f.val < 0 := lt_of_lt_of_le f.isLt (by
          change (if n + 3 = 0 then 1 else if n + 3 = 1 then 1 else
            if n + 3 = 2 then 2 else 0) ≤ 0
          rw [hz])
        exact False.elim (Nat.not_lt_zero _ h)

/-- All terms of the original language preserve standard numeral evaluation,
including arbitrary nesting of addition and multiplication. -/
theorem realize_term_numerals {α : Type*} (t : language.Term α) (env : α → ℕ) :
    t.realize (fun i => modelNumeral (M := M) (env i)) =
      modelNumeral (t.realize env) := by
  induction t with
  | var i => rfl
  | func f ts ih =>
    simp only [Term.realize_func, ih]
    exact model_function_numerals f _

end Models

/-- Define x ≤ y by ∃d, d+x=y using a genuine bound variable, so no free
variable can be captured by the auxiliary existential quantifier. -/
def leFormula (t u : T) : language.Formula ℕ :=
  (BoundedFormula.equal
    (.func (⟨0, by decide⟩ : language.Functions 2)
      ![.var (Sum.inr 0), t.relabel Sum.inl])
    (u.relabel Sum.inl)).ex

theorem realize_leFormula {M : Type*} [language.Structure M] (t u : T) (env : ℕ → M) :
    (leFormula t u).Realize env ↔ modelLE (t.realize env) (u.realize env) := by
  simp only [leFormula, Formula.Realize, BoundedFormula.realize_ex,
    BoundedFormula.Realize, Term.realize_relabel]
  apply exists_congr
  intro x
  let sx : Fin 1 → M := Fin.snoc (default : Fin 0 → M) x
  have he : (Sum.elim env (Fin.snoc (default : Fin 0 → M) x) ∘ Sum.inl : ℕ → M) = env := rfl
  rw [he]
  have heval :
      (.func (⟨0, by decide⟩ : language.Functions 2)
        ![.var (Sum.inr 0), t.relabel Sum.inl] : language.Term (ℕ ⊕ Fin 1)).realize
          (Sum.elim env sx) = modelAdd x (t.realize env) := by
    unfold modelAdd
    change Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 2)
        (fun j => (![.var (Sum.inr 0), t.relabel Sum.inl] j).realize (Sum.elim env sx)) =
      Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 2)
        ![x, t.realize env]
    apply congrArg (Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 2))
    funext j
    fin_cases j <;> simp [Term.realize_var, Term.realize_relabel, sx, Fin.snoc]
  rw [heval]

def boundedAll (i : ℕ) (bound : T) (φ : language.Formula ℕ) : language.Formula ℕ :=
  allV i ((leFormula (v i) bound).imp φ)

/-- A certificate that an actual formula is built from equalities, Boolean
connectives and bounded quantifiers. Bounds cannot contain their own binder. -/
inductive DeltaZero : language.Formula ℕ → Prop
  | falsum : DeltaZero .falsum
  | equal (t u : T) : DeltaZero (t.equal u)
  | imp {φ ψ} : DeltaZero φ → DeltaZero ψ → DeltaZero (φ.imp ψ)
  | all {i bound φ} : i ∉ bound.varFinset → DeltaZero φ → DeltaZero (boundedAll i bound φ)

theorem realize_term_update {M : Type*} [language.Structure M]
    (t : T) {i : ℕ} (hi : i ∉ t.varFinset) (env : ℕ → M) (x : M) :
    t.realize (Function.update env i x) = t.realize env := by
  let restricted : t.varFinset → M := fun j => env j
  have h1 := Term.realize_restrictVar (t := t) (f := id) (v := restricted)
    (Function.update env i x) (by
      intro j
      have hj : j.val ≠ i := by intro h; exact hi (h ▸ j.property)
      simp [restricted, Function.update, hj])
  have h2 := Term.realize_restrictVar (t := t) (f := id) (v := restricted)
    env (fun _ => rfl)
  exact h1.symm.trans h2

theorem realize_boundedAll {M : Type*} [language.Structure M]
    (i : ℕ) (bound : T) (φ : language.Formula ℕ) (hi : i ∉ bound.varFinset)
    (env : ℕ → M) :
    (boundedAll i bound φ).Realize env ↔
      ∀ x, modelLE x (bound.realize env) → φ.Realize (Function.update env i x) := by
  simp only [boundedAll, realize_allV, Formula.realize_imp, realize_leFormula,
    realize_v, Function.update_self, realize_term_update bound hi]

theorem modelLE_nat (x y : ℕ) : modelLE x y ↔ x ≤ y := by
  have h := model_le_numeral_iff (M := ℕ) x y
  simp only [model_numeral_nat] at h
  rw [h]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem numeral_update {M : Type*} [language.Structure M] (env : ℕ → ℕ) (i n : ℕ) :
    Function.update (fun j => modelNumeral (M := M) (env j)) i (modelNumeral n) =
      (fun j => modelNumeral (M := M) (Function.update env i n j)) := by
  funext j
  by_cases hj : j = i <;> simp [Function.update, hj]

/-- Bounded quantification stays within standard numerals, so every formula
certified by DeltaZero is absolute at standard numeral inputs. -/
theorem deltaZero_absolute {M : Type*} [language.Structure M] [Nonempty M] [M ⊨ robinson]
    {φ : language.Formula ℕ} (hφ : DeltaZero φ) (env : ℕ → ℕ) :
    φ.Realize (fun i => modelNumeral (M := M) (env i)) ↔ φ.Realize env := by
  induction hφ generalizing env with
  | falsum => rfl
  | equal t u =>
    simp only [Formula.realize_equal, realize_term_numerals, model_numeral_injective.eq_iff]
  | imp hφ hψ ihφ ihψ =>
    simp only [Formula.realize_imp, ihφ env, ihψ env]
  | @all i bound φ hi hφ ih =>
    rw [realize_boundedAll i bound φ hi, realize_boundedAll i bound φ hi]
    rw [realize_term_numerals]
    simp only [model_le_numeral_iff, modelLE_nat]
    constructor
    · intro h n hn
      have hm := h (modelNumeral n) ⟨n, hn, rfl⟩
      rw [numeral_update] at hm
      exact (ih (Function.update env i n)).mp hm
    · rintro h x ⟨n, hn, rfl⟩
      rw [numeral_update]
      exact (ih (Function.update env i n)).mpr (h n hn)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.realize_term_numerals
#check_upstream ClassicalTheorems.Progress.Arithmetic.deltaZero_absolute

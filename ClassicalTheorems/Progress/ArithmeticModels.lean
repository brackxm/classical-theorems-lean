/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Audit
import ClassicalTheorems.Statements.Arithmetic

/-! Concrete models of the exact seven-axiom Robinson theory used by the
Robinson-Q incompleteness theorem. No incompleteness theorem is assumed here. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
namespace ClassicalTheorems.Progress.Arithmetic
open ClassicalTheorems.Statements.Arithmetic

/-- Universal closure has its intended semantics for named free variables. -/
theorem realize_closeAll {L : _root_.FirstOrder.Language} {M : Type*}
    [L.Structure M] [Nonempty M] (φ : L.Formula ℕ) :
    M ⊨ closeAll φ ↔ ∀ env : ℕ → M, φ.Realize env := by
  rw [closeAll, Sentence.realize_not, Formula.realize_exClosure]
  constructor
  · intro h env
    by_contra hn
    apply h
    refine ⟨fun x => env x, ?_⟩
    exact (BoundedFormula.realize_restrictFreeVar (φ := φ.not) (f := id)
      (v' := env) (fun _ => rfl)).mpr hn
  · intro h ⟨env, hn⟩
    let fullEnv : ℕ → M := fun i => if hi : i ∈ φ.not.freeVarFinset
      then env ⟨i, hi⟩ else Classical.choice inferInstance
    have hn' : φ.not.Realize fullEnv :=
      (BoundedFormula.realize_restrictFreeVar (φ := φ.not) (f := id)
        (v' := fullEnv) (by
          intro i
          dsimp only [fullEnv]
          rw [dite_eq_left i.property]
          rfl)).mp hn
    exact hn' (h fullEnv)

theorem realize_allV {L : _root_.FirstOrder.Language} {M : Type*}
    [L.Structure M] (i : ℕ) (φ : L.Formula ℕ) (env : ℕ → M) :
    (allV i φ).Realize env ↔ ∀ x, φ.Realize (Function.update env i x) := by
  simp only [allV, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_relabel]
  apply forall_congr'
  intro x
  have he : (Sum.elim env (Fin.snoc default x ∘ Fin.castAdd 0) ∘
      fun j => if j = i then Sum.inr (0 : Fin 1) else Sum.inl j) =
      Function.update env i x := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update, Fin.snoc]
  rw [he]
  have hxs : (Fin.snoc (default : Fin 0 → M) x ∘ Fin.natAdd 1 : Fin 0 → M) =
      default := Subsingleton.elim _ _
  rw [hxs]

theorem realize_exV {L : _root_.FirstOrder.Language} {M : Type*}
    [L.Structure M] (i : ℕ) (φ : L.Formula ℕ) (env : ℕ → M) :
    (exV i φ).Realize env ↔ ∃ x, φ.Realize (Function.update env i x) := by
  simp [exV, realize_allV]

/-- Interpret the four symbols using supplied arithmetic operations. -/
@[instance_reducible] def structureOf {M : Type*} (z : M) (s : M → M) (a m : M → M → M) :
    language.Structure M where
  funMap {n} f xs := match n with
    | 0 => z
    | 1 => s (xs 0)
    | 2 => if f.val = 0 then a (xs 0) (xs 1) else m (xs 0) (xs 1)
    | n + 3 => False.elim (by simpa [language] using f.isLt)
  RelMap f _ := Empty.elim f

instance naturalStructure : language.Structure ℕ :=
  structureOf 0 Nat.succ (· + ·) (· * ·)

@[simp] theorem natural_zero (env : ℕ → ℕ) : zero.realize env = 0 := rfl
@[simp] theorem natural_succ (env : ℕ → ℕ) (t : T) :
    (succ t).realize env = Nat.succ (t.realize env) := rfl
@[simp] theorem natural_add (env : ℕ → ℕ) (t u : T) :
    (add t u).realize env = t.realize env + u.realize env := rfl
@[simp] theorem natural_mul (env : ℕ → ℕ) (t u : T) :
    (mul t u).realize env = t.realize env * u.realize env := rfl
@[simp] theorem realize_v {M : Type*} [language.Structure M] (env : ℕ → M) (i : ℕ) :
    (v i).realize env = env i := rfl

/-- The standard natural numbers satisfy the exact seven universally closed
axioms; in particular the Robinson-Q theorem’s consistency premise is inhabited. -/
instance naturalModelsRobinson : ℕ ⊨ robinson := by
  rw [Theory.model_iff]
  intro φ hφ
  simp only [robinson, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [realize_closeAll]; intro env
  all_goals simp [Formula.realize_equal, realize_exV]
  · omega
  · omega
  · exact Nat.mul_succ _ _

theorem robinson_satisfiable : robinson.IsSatisfiable :=
  Theory.Model.isSatisfiable ℕ

/-- The sentence expressing left multiplication by zero is an example of
an elementary fact that requires more than Robinson's seven axioms. -/
def zeroMultiplication : language.Sentence := closeAll ((mul zero (v 0)).equal zero)

theorem natural_zeroMultiplication : ℕ ⊨ zeroMultiplication := by
  rw [zeroMultiplication, realize_closeAll]
  intro env
  simp [Formula.realize_equal]

/-- A new element at infinity is fixed by successor. -/
def infiniteSucc : Option ℕ → Option ℕ := Option.map Nat.succ

def infiniteAdd : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a + b)
  | _, _ => none

/-- Multiplication by infinity on the right always gives infinity, including
zero times infinity. The Robinson recursion is on the right argument. -/
def infiniteMul : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a * b)
  | none, some 0 => some 0
  | _, _ => none

@[simp] theorem infinite_succ_ne_zero (x : Option ℕ) : infiniteSucc x ≠ some 0 := by
  cases x <;> simp [infiniteSucc]

theorem infinite_succ_injective : Function.Injective infiniteSucc := by
  intro x y h
  cases x <;> cases y <;> simp_all [infiniteSucc]

theorem infinite_predecessor (x : Option ℕ) (hx : x ≠ some 0) :
    ∃ y, x = infiniteSucc y := by
  cases x with
  | none => exact ⟨none, rfl⟩
  | some n =>
    cases n with
    | zero => exact False.elim (hx rfl)
    | succ n => exact ⟨some n, rfl⟩

@[simp] theorem infinite_add_zero (x : Option ℕ) : infiniteAdd x (some 0) = x := by
  cases x <;> simp [infiniteAdd]

@[simp] theorem infinite_add_succ (x y : Option ℕ) :
    infiniteAdd x (infiniteSucc y) = infiniteSucc (infiniteAdd x y) := by
  cases x <;> cases y <;> simp [infiniteAdd, infiniteSucc]
  omega

@[simp] theorem infinite_mul_zero (x : Option ℕ) : infiniteMul x (some 0) = some 0 := by
  cases x <;> simp [infiniteMul]

@[simp] theorem infinite_mul_succ (x y : Option ℕ) :
    infiniteMul x (infiniteSucc y) = infiniteAdd (infiniteMul x y) x := by
  cases x with
  | some n => cases y <;> simp [infiniteMul, infiniteAdd, infiniteSucc, Nat.mul_succ]
  | none =>
    cases y with
    | none => rfl
    | some n => cases n <;> rfl

instance infiniteStructure : language.Structure (Option ℕ) :=
  structureOf (some 0) infiniteSucc infiniteAdd infiniteMul

@[simp] theorem infinite_zero (env : ℕ → Option ℕ) : zero.realize env = some 0 := rfl
@[simp] theorem infinite_succ (env : ℕ → Option ℕ) (t : T) :
    (succ t).realize env = infiniteSucc (t.realize env) := rfl
@[simp] theorem infinite_add (env : ℕ → Option ℕ) (t u : T) :
    (add t u).realize env = infiniteAdd (t.realize env) (u.realize env) := rfl
@[simp] theorem infinite_mul (env : ℕ → Option ℕ) (t u : T) :
    (mul t u).realize env = infiniteMul (t.realize env) (u.realize env) := rfl

/-- This nonstandard model satisfies all seven axioms and refutes zero times
infinity being zero. No induction or additional arithmetic law is assumed. -/
instance infiniteModelsRobinson : Option ℕ ⊨ robinson := by
  rw [Theory.model_iff]
  intro φ hφ
  simp only [robinson, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rw [realize_closeAll]; intro env
  all_goals simp [Formula.realize_equal, realize_exV]
  · intro h
    exact infinite_succ_injective h
  · exact infinite_predecessor _

theorem infinite_not_zeroMultiplication : ¬ (Option ℕ ⊨ zeroMultiplication) := by
  rw [zeroMultiplication, realize_closeAll]
  intro h
  have hn := h (fun _ => none)
  simp [Formula.realize_equal, infiniteMul] at hn

/-- Robinson arithmetic itself has a concrete independent sentence. This is
weaker than essential incompleteness of every consistent effective extension. -/
theorem robinson_independent_sentence :
    (robinson ∪ {zeroMultiplication}).IsSatisfiable ∧
      (robinson ∪ {zeroMultiplication.not}).IsSatisfiable := by
  constructor
  · let : ℕ ⊨ robinson ∪ {zeroMultiplication} := by
      rw [Theory.model_iff]
      intro φ hφ
      rcases hφ with hφ | hφ
      · exact Theory.realize_sentence_of_mem robinson hφ
      · simpa only [Set.mem_singleton_iff.mp hφ] using natural_zeroMultiplication
    exact Theory.Model.isSatisfiable ℕ
  · let : Option ℕ ⊨ robinson ∪ {zeroMultiplication.not} := by
      rw [Theory.model_iff]
      intro φ hφ
      rcases hφ with hφ | hφ
      · exact Theory.realize_sentence_of_mem robinson hφ
      · rw [Set.mem_singleton_iff.mp hφ, Sentence.realize_not]
        exact infinite_not_zeroMultiplication
    exact Theory.Model.isSatisfiable (Option ℕ)

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_satisfiable
#check_upstream ClassicalTheorems.Progress.Arithmetic.natural_zeroMultiplication
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_independent_sentence

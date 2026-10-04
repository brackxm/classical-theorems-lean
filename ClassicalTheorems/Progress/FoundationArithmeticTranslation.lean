/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonSyntax
import ClassicalTheorems.Progress.ProgramWitnessMatrices

/-! Translate bounded witness matrices from the existing Foundation dependency
to the exact zero/successor/addition/multiplication language used by Robinson Q.
The translation preserves natural-number evaluation and records free variables
so auxiliary binders cannot capture inputs. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
open FFL FFL.FirstOrder
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
namespace ClassicalTheorems.Progress.Arithmetic

def foundationTerm {k : ℕ} (names : Fin k → ℕ) : ArithmeticSemiterm Empty k → T
  | .bvar i => v (names i)
  | .fvar x => Empty.elim x
  | .func .zero _ => zero
  | .func .one _ => succ zero
  | .func .add ts => add (foundationTerm names (ts 0)) (foundationTerm names (ts 1))
  | .func .mul ts => mul (foundationTerm names (ts 0)) (foundationTerm names (ts 1))

theorem foundationTerm_realize {k : ℕ} (names : Fin k → ℕ)
    (t : ArithmeticSemiterm Empty k) (env : ℕ → ℕ) :
    (foundationTerm names t).realize env = t.val (env ∘ names) Empty.elim := by
  induction t with
  | bvar i => rfl
  | fvar x => exact Empty.elim x
  | func f ts ih =>
    cases f
    · rfl
    · rfl
    · change (foundationTerm names (ts 0)).realize env + (foundationTerm names (ts 1)).realize env =
        (ts 0).val (env ∘ names) Empty.elim + (ts 1).val (env ∘ names) Empty.elim
      rw [ih 0, ih 1]
    · change (foundationTerm names (ts 0)).realize env * (foundationTerm names (ts 1)).realize env =
        (ts 0).val (env ∘ names) Empty.elim * (ts 1).val (env ∘ names) Empty.elim
      rw [ih 0, ih 1]

theorem foundationTerm_support {k : ℕ} (names : Fin k → ℕ)
    (t : ArithmeticSemiterm Empty k) :
    (foundationTerm names t).varFinset ⊆ Finset.univ.image names := by
  induction t with
  | bvar i => simp [foundationTerm, v, Term.varFinset]
  | fvar x => exact Empty.elim x
  | func f ts ih =>
    cases f
    · simp [foundationTerm, zero, Term.varFinset]
    · simp [foundationTerm, succ, zero, Term.varFinset]
    · simp only [foundationTerm, add, Term.varFinset, Finset.biUnion_subset_iff_forall_subset]
      intro i _
      fin_cases i <;> exact ih _
    · simp only [foundationTerm, mul, Term.varFinset, Finset.biUnion_subset_iff_forall_subset]
      intro i _
      fin_cases i <;> exact ih _

theorem fresh_name_ne {k : ℕ} (names : Fin k → ℕ) (i : Fin k) :
    names i ≠ freshNat (Finset.univ.image names) := by
  intro h
  apply freshNat_not_mem (Finset.univ.image names)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h⟩

theorem extended_names_eval {k : ℕ} (names : Fin k → ℕ) (env : ℕ → ℕ) (x : ℕ) :
    Function.update env (freshNat (Finset.univ.image names)) x ∘
      Matrix.vecCons (freshNat (Finset.univ.image names)) names =
        Matrix.vecCons x (env ∘ names) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Function.comp_def]
  | succ i => simp [Function.comp_def, Function.update_of_ne (fresh_name_ne names i)]

theorem extended_names_support {k : ℕ} (names : Fin k → ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.univ.image (Matrix.vecCons (freshNat (Finset.univ.image names)) names)) :
    s.erase (freshNat (Finset.univ.image names)) ⊆ Finset.univ.image names := by
  intro a ha
  obtain ⟨hne, ha⟩ := Finset.mem_erase.mp ha
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (hs ha)
  cases i using Fin.cases with
  | zero => exact False.elim (hne hi.symm)
  | succ i => exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

/-- A Foundation bounded formula has an equivalent certified bounded formula
in the project's arithmetic language. Only the named input variables occur
freely, even after translating nested bounded quantifiers. -/
theorem foundation_bounded_translation {k : ℕ} (φ : ArithmeticSemisentence k)
    (hφ : ℬ[<, ℒₒᵣ].Closure φ) :
    ∀ names : Fin k → ℕ, ∃ ψ : language.Formula ℕ,
      DeltaZero ψ ∧ ψ.freeVarFinset ⊆ Finset.univ.image names ∧
      ∀ env : ℕ → ℕ, ψ.Realize env ↔ φ.Evalb (env ∘ names) := by
  induction hφ with
  | verum k =>
    intro names
    refine ⟨(BoundedFormula.falsum : language.Formula ℕ).not,
      deltaZero_not .falsum, ?_, ?_⟩
    · simp [BoundedFormula.freeVarFinset]
    · intro env; simp [Formula.Realize, BoundedFormula.Realize]
  | falsum k =>
    intro names
    refine ⟨.falsum, .falsum, ?_, ?_⟩
    · simp [BoundedFormula.freeVarFinset]
    · intro env; rfl
  | rel r ts =>
    intro names
    cases r
    · refine ⟨(foundationTerm names (ts 0)).equal (foundationTerm names (ts 1)), .equal _ _, ?_, ?_⟩
      · exact (equal_support _ _).trans
          (Finset.union_subset (foundationTerm_support _ _) (foundationTerm_support _ _))
      · intro env
        simp only [Formula.realize_equal, foundationTerm_realize]
        rfl
    · obtain ⟨ψ, hψ, hs, hspec⟩ := exists_bounded_lt
        (foundationTerm names (ts 0)) (foundationTerm names (ts 1))
      refine ⟨ψ, hψ, hs.trans (Finset.union_subset
        (foundationTerm_support _ _) (foundationTerm_support _ _)), ?_⟩
      intro env
      rw [hspec, foundationTerm_realize, foundationTerm_realize]
      rfl
  | nrel r ts =>
    intro names
    cases r
    · refine ⟨((foundationTerm names (ts 0)).equal (foundationTerm names (ts 1))).not,
        deltaZero_not (.equal _ _), ?_, ?_⟩
      · rw [not_support]
        exact (equal_support _ _).trans
          (Finset.union_subset (foundationTerm_support _ _) (foundationTerm_support _ _))
      · intro env
        simp only [Formula.realize_not, Formula.realize_equal, foundationTerm_realize]
        rfl
    · obtain ⟨ψ, hψ, hs, hspec⟩ := exists_bounded_lt
        (foundationTerm names (ts 0)) (foundationTerm names (ts 1))
      refine ⟨ψ.not, deltaZero_not hψ, ?_, ?_⟩
      · rw [not_support]
        exact hs.trans (Finset.union_subset (foundationTerm_support _ _) (foundationTerm_support _ _))
      · intro env
        rw [Formula.realize_not, hspec, foundationTerm_realize, foundationTerm_realize]
        rfl
  | and hp hq ihp ihq =>
    intro names
    obtain ⟨ψ, hψ, hsψ, hspecψ⟩ := ihp names
    obtain ⟨χ, hχ, hsχ, hspecχ⟩ := ihq names
    refine ⟨ψ ⊓ χ, deltaZero_inf hψ hχ, ?_, ?_⟩
    · rw [inf_support]; exact Finset.union_subset hsψ hsχ
    · intro env; simp only [Formula.realize_inf, hspecψ, hspecχ]; rfl
  | or hp hq ihp ihq =>
    intro names
    obtain ⟨ψ, hψ, hsψ, hspecψ⟩ := ihp names
    obtain ⟨χ, hχ, hsχ, hspecχ⟩ := ihq names
    refine ⟨ψ ⊔ χ, deltaZero_sup hψ hχ, ?_, ?_⟩
    · rw [sup_support]; exact Finset.union_subset hsψ hsχ
    · intro env; simp only [Formula.realize_sup, hspecψ, hspecχ]; rfl
  | ball hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    intro names
    let d := freshNat (Finset.univ.image names)
    obtain ⟨ψ, hψ, hsψ, hspecψ⟩ := ih (Matrix.vecCons d names)
    have ht : d ∉ (foundationTerm names t).varFinset :=
      fun h => freshNat_not_mem _ (foundationTerm_support names t h)
    obtain ⟨allφ, exφ, hall, _, hsall, _, hspecall, _⟩ :=
      exists_strict_bounded_quantifiers d (foundationTerm names t) ψ ht hψ
    refine ⟨allφ, hall, ?_, ?_⟩
    · intro a ha
      obtain ⟨had, ha⟩ := Finset.mem_erase.mp (hsall ha)
      rcases Finset.mem_union.mp ha with ha | ha
      · exact foundationTerm_support _ _ ha
      · exact extended_names_support names _ hsψ (Finset.mem_erase.mpr ⟨had, ha⟩)
    · intro env
      rw [hspecall, foundationTerm_realize]
      simp only [hspecψ]
      dsimp only [d]
      simp only [extended_names_eval]
      simp [Semiformula.Operator.lt_def, Semiformula.eval_ball]
  | bexs hR ht hp ih =>
    obtain rfl := Set.mem_singleton_iff.mp hR
    obtain ⟨t, rfl⟩ := Rew.positive_iff.mp ht
    intro names
    let d := freshNat (Finset.univ.image names)
    obtain ⟨ψ, hψ, hsψ, hspecψ⟩ := ih (Matrix.vecCons d names)
    have ht : d ∉ (foundationTerm names t).varFinset :=
      fun h => freshNat_not_mem _ (foundationTerm_support names t h)
    obtain ⟨allφ, exφ, _, hex, _, hsex, _, hspecex⟩ :=
      exists_strict_bounded_quantifiers d (foundationTerm names t) ψ ht hψ
    refine ⟨exφ, hex, ?_, ?_⟩
    · intro a ha
      obtain ⟨had, ha⟩ := Finset.mem_erase.mp (hsex ha)
      rcases Finset.mem_union.mp ha with ha | ha
      · exact foundationTerm_support _ _ ha
      · exact extended_names_support names _ hsψ (Finset.mem_erase.mpr ⟨had, ha⟩)
    · intro env
      rw [hspecex, foundationTerm_realize]
      simp only [hspecψ]
      dsimp only [d]
      simp only [extended_names_eval]
      simp [Semiformula.Operator.lt_def, Semiformula.eval_bexs]

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.foundationTerm_realize
#check_upstream ClassicalTheorems.Progress.Arithmetic.foundation_bounded_translation

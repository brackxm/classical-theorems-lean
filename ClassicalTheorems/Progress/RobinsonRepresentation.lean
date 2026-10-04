/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonBounded

/-! Ground arithmetic representation and the Rosser witness comparison in
the original Robinson language. The `RobinsonProgramWitnesses` module
constructs the actual computation matrices used by the Rosser sentence. -/

noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

def numeralTerm {α : Type*} : ℕ → language.Term α
  | 0 => .func (⟨0, by decide⟩ : language.Functions 0) Fin.elim0
  | n + 1 => .func (⟨0, by decide⟩ : language.Functions 1) ![numeralTerm n]

theorem realize_numeralTerm {M α : Type*} [language.Structure M]
    (env : α → M) (n : ℕ) :
    (numeralTerm n).realize env = modelNumeral (M := M) n := by
  induction n with
  | zero =>
    change Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 0)
      (fun i => (Fin.elim0 i : language.Term α).realize env) = modelZero
    unfold modelZero
    apply congrArg (Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 0))
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    change Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 1)
      (fun i => (![numeralTerm n] i).realize env) = modelSucc (modelNumeral n)
    unfold modelSucc
    apply congrArg (Structure.funMap (L := language) (⟨0, by decide⟩ : language.Functions 1))
    funext i
    fin_cases i
    exact ih

/-- Substitute closed numeral terms for all free variables, obtaining an
actual sentence rather than universally quantifying over nonstandard inputs. -/
def numeralInstance (φ : language.Formula ℕ) (env : ℕ → ℕ) : language.Sentence :=
  φ.subst (fun i => numeralTerm (env i))

theorem realize_numeralInstance {M : Type*} [language.Structure M]
    (φ : language.Formula ℕ) (env : ℕ → ℕ) :
    M ⊨ numeralInstance φ env ↔ φ.Realize (fun i => modelNumeral (M := M) (env i)) := by
  simp only [numeralInstance, Sentence.Realize, Formula.Realize,
    BoundedFormula.realize_subst, realize_numeralTerm]

theorem robinson_models_deltaZero_instance {φ : language.Formula ℕ}
    (hφ : DeltaZero φ) (env : ℕ → ℕ) (hNat : φ.Realize env) :
    robinson ⊨ᵇ numeralInstance φ env := by
  rw [Theory.models_sentence_iff]
  intro M
  rw [realize_numeralInstance]
  exact (deltaZero_absolute hφ env).mpr hNat

theorem robinson_models_not_deltaZero_instance {φ : language.Formula ℕ}
    (hφ : DeltaZero φ) (env : ℕ → ℕ) (hNat : ¬ φ.Realize env) :
    robinson ⊨ᵇ (numeralInstance φ env).not := by
  rw [Theory.models_sentence_iff]
  intro M
  rw [Sentence.realize_not, realize_numeralInstance, deltaZero_absolute hφ env]
  exact hNat

/-- Existential closures of bounded formulas have positive representation. -/
inductive SigmaOne : language.Formula ℕ → Prop
  | bounded {φ} : DeltaZero φ → SigmaOne φ
  | ex {i φ} : SigmaOne φ → SigmaOne (exV i φ)

theorem sigmaOne_positive {M : Type*} [language.Structure M] [Nonempty M] [M ⊨ robinson]
    {φ : language.Formula ℕ} (hφ : SigmaOne φ) (env : ℕ → ℕ) (hNat : φ.Realize env) :
    φ.Realize (fun i => modelNumeral (M := M) (env i)) := by
  induction hφ generalizing env with
  | bounded hφ => exact (deltaZero_absolute hφ env).mpr hNat
  | @ex i φ hφ ih =>
    rw [realize_exV] at hNat ⊢
    obtain ⟨n, hn⟩ := hNat
    refine ⟨modelNumeral n, ?_⟩
    rw [numeral_update]
    exact ih (Function.update env i n) hn

theorem robinson_models_sigmaOne_instance {φ : language.Formula ℕ}
    (hφ : SigmaOne φ) (env : ℕ → ℕ) (hNat : φ.Realize env) :
    robinson ⊨ᵇ numeralInstance φ env := by
  rw [Theory.models_sentence_iff]
  intro M
  rw [realize_numeralInstance]
  exact sigmaOne_positive hφ env hNat

theorem formula_realize_congr {M : Type*} [language.Structure M]
    (φ : language.Formula ℕ) {env₁ env₂ : ℕ → M}
    (h : ∀ i ∈ φ.freeVarFinset, env₁ i = env₂ i) : φ.Realize env₁ ↔ φ.Realize env₂ := by
  let restricted : φ.freeVarFinset → M := fun i => env₁ i
  have h1 := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id) (v := restricted)
    (xs := (default : Fin 0 → M))
    env₁ (fun _ => rfl)
  have h2 := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id) (v := restricted)
    (xs := (default : Fin 0 → M))
    env₂ (fun i => h i i.property)
  exact h1.symm.trans h2

/-- Prefer a positive witness only when there is no smaller or equal negative
witness. Renaming is capture-avoiding in mathlib's actual formula syntax. -/
def rosserFormula (i j : ℕ) (positive negative : language.Formula ℕ) : language.Formula ℕ :=
  exV i (positive ⊓ allV j ((leFormula (v j) (v i)).imp
    (Formula.relabel (fun k => if k = i then j else k) negative).not))

def rosserComparison {M : Type*} [language.Structure M] (positive negative : M → Prop) : Prop :=
  ∃ a, positive a ∧ ∀ b, modelLE b a → ¬ negative b

theorem realize_rosserFormula {M : Type*} [language.Structure M]
    (i j : ℕ) (positive negative : language.Formula ℕ) (hij : i ≠ j)
    (hfresh : j ∉ negative.freeVarFinset) (env : ℕ → M) :
    (rosserFormula i j positive negative).Realize env ↔
      rosserComparison (fun a => positive.Realize (Function.update env i a))
        (fun b => negative.Realize (Function.update env i b)) := by
  simp only [rosserFormula, realize_exV, Formula.realize_inf, realize_allV,
    Formula.realize_imp, realize_leFormula, realize_v, Formula.realize_not,
    Formula.realize_relabel, rosserComparison]
  apply exists_congr
  intro a
  apply and_congr_right
  intro _
  apply forall_congr'
  intro b
  simp only [Function.update_self, Function.update_of_ne hij]
  apply imp_congr_right
  intro _
  apply not_congr
  apply formula_realize_congr
  intro k hk
  by_cases hki : k = i
  · subst k
    simp [Function.update]
  · have hkj : k ≠ j := by intro h; exact hfresh (h ▸ hk)
    simp [Function.comp_apply, hki, hkj, Function.update]

section Models
variable {M : Type*} [language.Structure M] [Nonempty M] [M ⊨ robinson]

theorem rosser_comparison_positive (p q : ℕ → Prop) (P Q : M → Prop)
    (hp : ∀ n, P (modelNumeral n) ↔ p n) (hq : ∀ n, Q (modelNumeral n) ↔ q n)
    (hpos : ∃ n, p n) (hneg : ∀ n, ¬ q n) : rosserComparison P Q := by
  obtain ⟨n, hn⟩ := hpos
  refine ⟨modelNumeral n, (hp n).mpr hn, ?_⟩
  intro b hb hQ
  obtain ⟨k, hk, rfl⟩ := (model_le_numeral_iff b n).mp hb
  exact hneg k ((hq k).mp hQ)

theorem rosser_comparison_negative (p q : ℕ → Prop) (P Q : M → Prop)
    (hp : ∀ n, P (modelNumeral n) ↔ p n) (hq : ∀ n, Q (modelNumeral n) ↔ q n)
    (hpos : ∀ n, ¬ p n) (hneg : ∃ n, q n) : ¬ rosserComparison P Q := by
  obtain ⟨n, hn⟩ := hneg
  rintro ⟨a, ha, hcomp⟩
  rcases model_le_total_numeral a n with hsmall | hlarge
  · obtain ⟨k, hk, rfl⟩ := (model_le_numeral_iff a n).mp hsmall
    exact hpos k ((hp k).mp ha)
  · exact hcomp (modelNumeral n) hlarge ((hq n).mpr hn)

end Models
end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_models_deltaZero_instance
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_models_not_deltaZero_instance
#check_upstream ClassicalTheorems.Progress.Arithmetic.robinson_models_sigmaOne_instance
#check_upstream ClassicalTheorems.Progress.Arithmetic.realize_rosserFormula
#check_upstream ClassicalTheorems.Progress.Arithmetic.rosser_comparison_positive
#check_upstream ClassicalTheorems.Progress.Arithmetic.rosser_comparison_negative

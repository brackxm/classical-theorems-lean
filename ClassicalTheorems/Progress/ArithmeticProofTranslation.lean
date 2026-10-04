/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofLanguage
import Mathlib.ModelTheory.Semantics
import Mathlib.Data.Fin.Tuple.Basic

/-! Translate the project's first-order syntax to Foundation while preserving
all four primitive arithmetic functions and genuine equality. Mathlib appends
bound variables; Foundation prepends them. Reversing their finite indices keeps
nested quantifiers and their scopes aligned. -/

noncomputable section
open Classical
open FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

def toProofTerm {α : Type*} {k : ℕ} : language.Term (α ⊕ Fin k) →
    FFL.FirstOrder.Semiterm proofLanguage α k
  | .var (.inl a) => .fvar a
  | .var (.inr i) => .bvar i.rev
  | .func f ts => .func f (fun i => toProofTerm (ts i))

def toProofFormula {α : Type*} : {k : ℕ} → language.BoundedFormula α k →
    FFL.FirstOrder.Semiformula proofLanguage α k
  | _, .falsum => ⊥
  | _, .equal t u => .rel proofEq ![toProofTerm t, toProofTerm u]
  | _, .rel r _ => Empty.elim r
  | _, .imp φ ψ => toProofFormula φ 🡒 toProofFormula ψ
  | _, .all φ => .all (toProofFormula φ)

def toProofSentence (φ : language.Sentence) : FFL.FirstOrder.Sentence proofLanguage :=
  toProofFormula φ

section Semantics
variable {M α : Type*} [language.Structure M] [FFL.FirstOrder.Tarski.Structure proofLanguage M]

theorem toProofTerm_realize {k : ℕ} (t : language.Term (α ⊕ Fin k))
    (env : α → M) (xs : Fin k → M)
    (hfunc : ∀ {n} (f : language.Functions n) (ys : Fin n → M),
      FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f ys = Structure.funMap f ys) :
    (toProofTerm t).val (xs ∘ Fin.rev) env = t.realize (Sum.elim env xs) := by
  induction t with
  | var a => cases a <;> simp [toProofTerm, Term.realize]
  | func f ts ih =>
    change FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f
      (fun i => (toProofTerm (ts i)).val (xs ∘ Fin.rev) env) =
        Structure.funMap f (fun i => (ts i).realize (Sum.elim env xs))
    rw [hfunc]
    congr 1
    funext i
    exact ih i

omit [language.Structure M] [FFL.FirstOrder.Tarski.Structure proofLanguage M] in
theorem snoc_reverse {k : ℕ} (xs : Fin k → M) (x : M) :
    Fin.snoc xs x ∘ Fin.rev = Matrix.vecCons x (xs ∘ Fin.rev) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [Function.comp_def]
  | succ i => simp [Function.comp_def, Fin.rev_succ]

theorem toProofFormula_realize {k : ℕ} (φ : language.BoundedFormula α k)
    (env : α → M) (xs : Fin k → M)
    (hfunc : ∀ {n} (f : language.Functions n) (ys : Fin n → M),
      FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f ys = Structure.funMap f ys)
    (heq : ∀ ys : Fin 2 → M,
      FFL.FirstOrder.Tarski.Structure.rel (L := proofLanguage) proofEq ys ↔ ys 0 = ys 1) :
    (toProofFormula φ).Eval (xs ∘ Fin.rev) env ↔ φ.Realize env xs := by
  induction φ with
  | falsum => rfl
  | equal t u =>
    simp only [toProofFormula, FFL.FirstOrder.Semiformula.eval_rel, heq,
      Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      toProofTerm_realize _ _ _ hfunc, BoundedFormula.Realize]
  | rel r ts => cases r
  | imp φ ψ ihφ ihψ =>
    simp only [toProofFormula, LogicalConnective.HomClass.map_imply,
      BoundedFormula.realize_imp, ihφ, ihψ]
    rfl
  | all φ ih =>
    simp only [toProofFormula, BoundedFormula.realize_all]
    apply forall_congr'
    intro x
    have h := ih (Fin.snoc xs x)
    rw [snoc_reverse] at h
    exact h

end Semantics

/-- Interpret Foundation's equality symbol as actual equality, retaining the
original interpretation of every arithmetic function. -/
@[instance_reducible] def exportProofStructure (M : Type*) [language.Structure M] :
    FFL.FirstOrder.Tarski.Structure proofLanguage M where
  func := fun {_} f ys => Structure.funMap (L := language) f ys
  rel := fun {n} _ ys => match n, ys with
    | 2, ys => ys 0 = ys 1
    | _, _ => False

@[instance_reducible] def importProofStructure (M : Type*) [FFL.FirstOrder.Tarski.Structure proofLanguage M] :
    language.Structure M where
  funMap := fun {_} f ys => FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f ys
  RelMap := fun r _ => Empty.elim r

theorem exportProofStructure_eq (M : Type*) [language.Structure M] :
    @FFL.FirstOrder.Tarski.Structure.Eq proofLanguage M (exportProofStructure M) _ := by
  let := exportProofStructure M
  change FFL.FirstOrder.Tarski.Structure.Eq proofLanguage M
  refine ⟨?_⟩
  intro a b
  rfl

theorem proof_relation_eq {M : Type*} [FFL.FirstOrder.Tarski.Structure proofLanguage M]
    [FFL.FirstOrder.Tarski.Structure.Eq proofLanguage M] (ys : Fin 2 → M) :
    FFL.FirstOrder.Tarski.Structure.rel (L := proofLanguage) proofEq ys ↔ ys 0 = ys 1 := by
  exact FFL.FirstOrder.Tarski.Structure.eq_lang (L := proofLanguage) (v := ys)

theorem toProofSentence_realize {M : Type*} [language.Structure M]
    [FFL.FirstOrder.Tarski.Structure proofLanguage M] (φ : language.Sentence)
    (hfunc : ∀ {n} (f : language.Functions n) (ys : Fin n → M),
      FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f ys = Structure.funMap f ys)
    (heq : ∀ ys : Fin 2 → M,
      FFL.FirstOrder.Tarski.Structure.rel (L := proofLanguage) proofEq ys ↔ ys 0 = ys 1) :
    (toProofSentence φ).Realize M ↔ M ⊨ φ := by
  have h := toProofFormula_realize φ (Empty.elim : Empty → M) (default : Fin 0 → M) hfunc heq
  have he : (Empty.elim : Empty → M) = default := Subsingleton.elim _ _
  simpa only [toProofSentence, FFL.FirstOrder.Semiformula.Realize,
    Sentence.Realize, Formula.Realize, Matrix.empty_eq, he] using h

/-- Translate the original axioms and add only the usual logical equality
axioms. No additional arithmetic axioms are introduced. -/
def toProofTheory (theory : language.Theory) : FFL.FirstOrder.Theory proofLanguage :=
  toProofSentence '' theory ∪ 𝗘𝗤 proofLanguage

theorem toProofTheory_models {M : Type*} [Nonempty M] [language.Structure M]
    [FFL.FirstOrder.Tarski.Structure proofLanguage M]
    [FFL.FirstOrder.Tarski.Structure.Eq proofLanguage M] (theory : language.Theory)
    (hfunc : ∀ {n} (f : language.Functions n) (ys : Fin n → M),
      FFL.FirstOrder.Tarski.Structure.func (L := proofLanguage) f ys = Structure.funMap f ys) :
    M↓[proofLanguage] ⊧* toProofTheory theory ↔ M ⊨ theory := by
  rw [FFL.FirstOrder.models_theory_iff, Theory.model_iff]
  constructor
  · intro h φ hφ
    exact (toProofSentence_realize φ hfunc proof_relation_eq).mp
      (h _ (Or.inl ⟨φ, hφ, rfl⟩))
  · intro h φ hφ
    rcases hφ with ⟨ψ, hψ, rfl⟩ | hφ
    · exact (toProofSentence_realize ψ hfunc proof_relation_eq).mpr (h ψ hψ)
    · exact FFL.FirstOrder.models_of_mem (T := 𝗘𝗤 proofLanguage) hφ

/-- Foundation's equality-model quotient and the two concrete structure
conversions identify semantic consequences in the two proof languages. -/
theorem toProofTheory_consequence (theory : language.Theory) (φ : language.Sentence) :
    toProofTheory theory ⊨[FFL.FirstOrder.Tarski.SmallStruc proofLanguage] toProofSentence φ ↔
      theory ⊨ᵇ φ := by
  rw [FFL.FirstOrder.consequence_iff_eq_of_models_eq
    (T := toProofTheory theory) (σ := toProofSentence φ) (fun M _ _ hM =>
    FFL.FirstOrder.models_theory_iff.mpr (fun ψ hψ =>
      FFL.FirstOrder.models_theory_iff.mp hM ψ (Or.inr hψ)))]
  constructor
  · intro h
    apply Theory.models_sentence_iff.mpr
    intro M
    let := exportProofStructure M
    let := exportProofStructure_eq M
    have hm : M↓[proofLanguage] ⊧* toProofTheory theory :=
      (toProofTheory_models theory (fun _ _ => rfl)).mpr inferInstance
    exact (toProofSentence_realize φ (fun _ _ => rfl) proof_relation_eq).mp (h M hm)
  · intro h M _ _ _ hm
    let := importProofStructure M
    have hmodel : M ⊨ theory :=
      (toProofTheory_models theory (fun _ _ => rfl)).mp hm
    let := hmodel
    exact (toProofSentence_realize φ (fun _ _ => rfl) proof_relation_eq).mpr
      (h.realize_sentence M)

/-- The actual Foundation calculus proves precisely the original theory's
semantic consequences after translation. -/
theorem toProofTheory_provable (theory : language.Theory) (φ : language.Sentence) :
    toProofTheory theory ⊢ toProofSentence φ ↔ theory ⊨ᵇ φ := by
  rw [← toProofTheory_consequence]
  exact ⟨FFL.FirstOrder.Theory.Proof.sound, FFL.FirstOrder.Theory.Proof.complete.{0, 0}⟩

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofTerm_realize
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofFormula_realize
#check_upstream ClassicalTheorems.Progress.Arithmetic.exportProofStructure_eq
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofSentence_realize
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofTheory_models
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofTheory_consequence
#check_upstream ClassicalTheorems.Progress.Arithmetic.toProofTheory_provable

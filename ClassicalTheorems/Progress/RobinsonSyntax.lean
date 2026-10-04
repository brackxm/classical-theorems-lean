/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.RobinsonRepresentation

/-! Free-variable bookkeeping for arithmetic witness translations. -/
noncomputable section
open Classical
open _root_.FirstOrder.Language ClassicalTheorems.Statements.FirstOrder
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

theorem term_relabel_support {α β γ δ : Type*} [DecidableEq α] [DecidableEq γ]
    (t : language.Term (α ⊕ β)) (f : α ⊕ β → γ ⊕ δ)
    (s : Finset γ) (h : ∀ a, Sum.inl a ∈ t.varFinset →
      ∀ c, f (Sum.inl a) = Sum.inl c → c ∈ s)
    (hb : ∀ b c, f (Sum.inr b) ≠ Sum.inl c) :
    (t.relabel f).varFinsetLeft ⊆ s := by
  induction t with
  | var a =>
    cases a with
    | inl a =>
      cases hf : f (Sum.inl a) with
      | inl c => simpa [Term.relabel, hf, Term.varFinsetLeft] using h a (by simp [Term.varFinset]) c hf
      | inr d => simp [Term.relabel, hf, Term.varFinsetLeft]
    | inr b =>
      cases hf : f (Sum.inr b) with
      | inl c => exact False.elim (hb b c hf)
      | inr d => simp [Term.relabel, hf, Term.varFinsetLeft]
  | func f' ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, Finset.biUnion_subset_iff_forall_subset]
    intro i _
    apply ih i
    intro a ha c hc
    exact h a (by simp only [Term.varFinset, Finset.mem_biUnion]; exact ⟨i, Finset.mem_univ _, ha⟩) c hc

theorem term_inl_mem_iff {α β : Type*} [DecidableEq α]
    (t : language.Term (α ⊕ β)) (a : α) :
    Sum.inl a ∈ t.varFinset ↔ a ∈ t.varFinsetLeft := by
  classical
  induction t with
  | var x => cases x <;> simp [Term.varFinset, Term.varFinsetLeft]
  | func f ts ih => simp [Term.varFinset, Term.varFinsetLeft, ih]

theorem formula_relabel_support {α β : Type*} [DecidableEq α] [DecidableEq β]
    {k n : ℕ} (φ : language.BoundedFormula α k) (f : α → β ⊕ Fin n)
    (s : Finset β) (h : ∀ a ∈ φ.freeVarFinset, ∀ b, f a = Sum.inl b → b ∈ s) :
    (φ.relabel f).freeVarFinset ⊆ s := by
  induction φ with
  | falsum => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset]
  | equal t u =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel,
      BoundedFormula.freeVarFinset, Finset.union_subset_iff]
    constructor
    · apply term_relabel_support
      · intro a ha b hb
        apply h a (Finset.mem_union_left _ ((term_inl_mem_iff _ _).mp ha)) b
        cases hf : f a <;> simp [BoundedFormula.relabelAux, hf] at hb ⊢
        exact hb
      · intro b c; simp [BoundedFormula.relabelAux]
    · apply term_relabel_support
      · intro a ha b hb
        apply h a (Finset.mem_union_right _ ((term_inl_mem_iff _ _).mp ha)) b
        cases hf : f a <;> simp [BoundedFormula.relabelAux, hf] at hb ⊢
        exact hb
      · intro b c; simp [BoundedFormula.relabelAux]
  | rel r ts => cases r
  | imp φ ψ ihφ ihψ =>
    simp only [BoundedFormula.relabel_imp, BoundedFormula.freeVarFinset, Finset.union_subset_iff]
    exact ⟨ihφ (fun a ha => h a (Finset.mem_union_left _ ha)),
      ihψ (fun a ha => h a (Finset.mem_union_right _ ha))⟩
  | all φ ih =>
    simpa only [BoundedFormula.relabel_all, BoundedFormula.freeVarFinset] using ih h

theorem allV_support (i : ℕ) (φ : language.Formula ℕ) :
    (allV i φ).freeVarFinset ⊆ φ.freeVarFinset.erase i := by
  apply formula_relabel_support
  intro a ha b hb
  by_cases hai : a = i
  · simp [hai] at hb
  · simp only [ite_eq_right hai, Sum.inl.injEq] at hb
    subst b
    exact Finset.mem_erase.mpr ⟨hai, ha⟩

theorem relabel_term_support {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (t : language.Term α) (f : α → β ⊕ γ) (s : Finset β)
    (h : ∀ a ∈ t.varFinset, ∀ b, f a = Sum.inl b → b ∈ s) :
    (t.relabel f).varFinsetLeft ⊆ s := by
  induction t with
  | var a =>
    cases hf : f a with
    | inl b => simpa [Term.relabel, hf, Term.varFinsetLeft] using h a (by simp [Term.varFinset]) b hf
    | inr b => simp [Term.relabel, hf, Term.varFinsetLeft]
  | func f' ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, Finset.biUnion_subset_iff_forall_subset]
    intro i _
    apply ih i
    intro a ha b hb
    exact h a (by simp only [Term.varFinset, Finset.mem_biUnion]; exact ⟨i, Finset.mem_univ _, ha⟩) b hb

theorem equal_support (t u : T) :
    (t.equal u).freeVarFinset ⊆ t.varFinset ∪ u.varFinset := by
  simp only [Term.equal, Term.bdEqual, BoundedFormula.freeVarFinset, Finset.union_subset_iff]
  constructor
  · apply relabel_term_support
    intro a ha b hb
    cases hb
    exact Finset.mem_union_left _ ha
  · apply relabel_term_support
    intro a ha b hb
    cases hb
    exact Finset.mem_union_right _ ha

theorem not_support (φ : language.Formula ℕ) :
    φ.not.freeVarFinset = φ.freeVarFinset := by
  simp [BoundedFormula.freeVarFinset]

theorem inf_support (φ ψ : language.Formula ℕ) :
    (φ ⊓ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change ((φ.imp ψ.not).not).freeVarFinset = _
  simp [BoundedFormula.freeVarFinset]

theorem sup_support (φ ψ : language.Formula ℕ) :
    (φ ⊔ ψ).freeVarFinset = φ.freeVarFinset ∪ ψ.freeVarFinset := by
  change (φ.not.imp ψ).freeVarFinset = _
  simp [BoundedFormula.freeVarFinset]

theorem leFormula_support (t u : T) :
    (leFormula t u).freeVarFinset ⊆ t.varFinset ∪ u.varFinset := by
  have ht := relabel_term_support t (Sum.inl : ℕ → ℕ ⊕ Fin 1) t.varFinset
    (by intro a ha b hb; cases hb; exact ha)
  have hu := relabel_term_support u (Sum.inl : ℕ → ℕ ⊕ Fin 1) u.varFinset
    (by intro a ha b hb; cases hb; exact ha)
  simp only [leFormula, BoundedFormula.ex, BoundedFormula.not,
    BoundedFormula.freeVarFinset, Finset.union_empty, Term.varFinsetLeft]
  intro a ha
  simp only [Finset.mem_union, Finset.mem_biUnion] at ha ⊢
  rcases ha with ⟨i, _, hi⟩ | ha
  · fin_cases i
    · simp [Term.varFinsetLeft] at hi
    · exact Or.inl (ht hi)
  · exact Or.inr (hu ha)

theorem boundedAll_support (i : ℕ) (bound : T) (φ : language.Formula ℕ) :
    (boundedAll i bound φ).freeVarFinset ⊆ (bound.varFinset ∪ φ.freeVarFinset).erase i := by
  intro a ha
  have h := (Finset.mem_erase.mp (allV_support i _ ha))
  refine Finset.mem_erase.mpr ⟨h.1, ?_⟩
  rcases Finset.mem_union.mp h.2 with hle | hφ
  · have hle := leFormula_support (v i) bound hle
    rcases Finset.mem_union.mp hle with hv | hb
    · simp only [v, Term.varFinset, Finset.mem_singleton] at hv
      exact False.elim (h.1 hv)
    · exact Finset.mem_union_left _ hb
  · exact Finset.mem_union_right _ hφ

theorem deltaZero_not {φ : language.Formula ℕ} (h : DeltaZero φ) : DeltaZero φ.not :=
  .imp h .falsum

theorem deltaZero_inf {φ ψ : language.Formula ℕ} (hφ : DeltaZero φ) (hψ : DeltaZero ψ) :
    DeltaZero (φ ⊓ ψ) := deltaZero_not (.imp hφ (deltaZero_not hψ))

theorem deltaZero_sup {φ ψ : language.Formula ℕ} (hφ : DeltaZero φ) (hψ : DeltaZero ψ) :
    DeltaZero (φ ⊔ ψ) := .imp (deltaZero_not hφ) hψ

def freshNat (s : Finset ℕ) : ℕ := s.sup id + 1

theorem freshNat_not_mem (s : Finset ℕ) : freshNat s ∉ s := by
  intro h
  have := Finset.le_sup (f := id) h
  unfold freshNat at this
  simp only [id_eq] at this
  omega

theorem succ_support (t : T) : (succ t).varFinset ⊆ t.varFinset := by
  simp only [succ, Term.varFinset, Finset.biUnion_subset_iff_forall_subset]
  intro i _
  fin_cases i
  exact Finset.Subset.refl _

theorem add_support (t u : T) : (add t u).varFinset ⊆ t.varFinset ∪ u.varFinset := by
  simp only [add, Term.varFinset, Finset.biUnion_subset_iff_forall_subset]
  intro i _
  fin_cases i
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

/-- Strict comparison has a bounded definition in the original language;
its auxiliary difference witness is at most the right-hand term. -/
theorem exists_bounded_lt (t u : T) :
    ∃ φ : language.Formula ℕ, DeltaZero φ ∧
      φ.freeVarFinset ⊆ t.varFinset ∪ u.varFinset ∧
      ∀ env : ℕ → ℕ, φ.Realize env ↔ t.realize env < u.realize env := by
  let s := t.varFinset ∪ u.varFinset
  let d := freshNat s
  have hd : d ∉ s := freshNat_not_mem s
  have ht : d ∉ t.varFinset := fun h => hd (Finset.mem_union_left _ h)
  have hu : d ∉ u.varFinset := fun h => hd (Finset.mem_union_right _ h)
  let eq : language.Formula ℕ := (add (v d) (succ t)).equal u
  let φ := (boundedAll d u eq.not).not
  refine ⟨φ, deltaZero_not (.all hu (deltaZero_not (.equal _ _))), ?_, ?_⟩
  · intro a ha
    have ha := boundedAll_support d u eq.not (by simpa [φ, not_support] using ha)
    obtain ⟨had, ha⟩ := Finset.mem_erase.mp ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Finset.mem_union_right _ ha
    · have heq : a ∈ eq.freeVarFinset := by simpa [not_support] using ha
      rcases Finset.mem_union.mp (equal_support _ _ heq) with ha | ha
      · rcases Finset.mem_union.mp (add_support _ _ ha) with ha | ha
        · have had' : a = d := by simpa [v, Term.varFinset] using ha
          exact False.elim (had had')
        · exact Finset.mem_union_left _ (succ_support _ ha)
      · exact Finset.mem_union_right _ ha
  · intro env
    simp only [φ, Formula.realize_not, realize_boundedAll d u eq.not hu,
      Formula.realize_not, Formula.realize_equal, eq, natural_add, natural_succ,
      realize_v, Function.update_self, realize_term_update t ht, realize_term_update u hu,
      modelLE_nat, not_forall, not_not]
    constructor
    · rintro ⟨x, _, hx⟩
      omega
    · intro h
      refine ⟨u.realize env - (t.realize env + 1), ?_, ?_⟩ <;> omega

/-- Both strict bounded quantifiers can be translated using the certified
non-strict bounds, without introducing a new relation symbol. -/
theorem exists_strict_bounded_quantifiers (i : ℕ) (bound : T)
    (ψ : language.Formula ℕ) (hi : i ∉ bound.varFinset) (hψ : DeltaZero ψ) :
    ∃ allφ exφ : language.Formula ℕ,
      DeltaZero allφ ∧ DeltaZero exφ ∧
      allφ.freeVarFinset ⊆ (bound.varFinset ∪ ψ.freeVarFinset).erase i ∧
      exφ.freeVarFinset ⊆ (bound.varFinset ∪ ψ.freeVarFinset).erase i ∧
      (∀ env : ℕ → ℕ, allφ.Realize env ↔
        ∀ x < bound.realize env, ψ.Realize (Function.update env i x)) ∧
      (∀ env : ℕ → ℕ, exφ.Realize env ↔
        ∃ x < bound.realize env, ψ.Realize (Function.update env i x)) := by
  obtain ⟨lt, hlt, hs, hspec⟩ := exists_bounded_lt (v i) bound
  let allφ := boundedAll i bound (lt.imp ψ)
  let exφ := (boundedAll i bound (lt ⊓ ψ).not).not
  refine ⟨allφ, exφ, .all hi (.imp hlt hψ),
    deltaZero_not (.all hi (deltaZero_not (deltaZero_inf hlt hψ))), ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨hai, ha⟩ := Finset.mem_erase.mp (boundedAll_support i bound (lt.imp ψ) ha)
    refine Finset.mem_erase.mpr ⟨hai, ?_⟩
    simp only [BoundedFormula.freeVarFinset, Finset.mem_union] at ha
    rcases ha with hb | hl | hp
    · exact Finset.mem_union_left _ hb
    · rcases Finset.mem_union.mp (hs hl) with hv | hb
      · have : a = i := by simpa [v, Term.varFinset] using hv
        exact False.elim (hai this)
      · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ hp
  · intro a ha
    have ha' : a ∈ (boundedAll i bound (lt ⊓ ψ).not).freeVarFinset := by
      simpa [exφ, not_support] using ha
    obtain ⟨hai, ha⟩ := Finset.mem_erase.mp (boundedAll_support i bound _ ha')
    refine Finset.mem_erase.mpr ⟨hai, ?_⟩
    simp only [not_support, inf_support, Finset.mem_union] at ha
    rcases ha with hb | hl | hp
    · exact Finset.mem_union_left _ hb
    · rcases Finset.mem_union.mp (hs hl) with hv | hb
      · have : a = i := by simpa [v, Term.varFinset] using hv
        exact False.elim (hai this)
      · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ hp
  · intro env
    simp only [allφ, realize_boundedAll i bound _ hi, Formula.realize_imp,
      hspec, realize_v, Function.update_self, realize_term_update bound hi, modelLE_nat]
    constructor
    · intro h x hx; exact h x (Nat.le_of_lt hx) hx
    · intro h x _ hx; exact h x hx
  · intro env
    simp only [exφ, Formula.realize_not, realize_boundedAll i bound _ hi,
      Formula.realize_not, Formula.realize_inf, hspec, realize_v, Function.update_self,
      realize_term_update bound hi, modelLE_nat, not_forall, not_not]
    constructor
    · rintro ⟨x, _, hx, hψ⟩; exact ⟨x, hx, hψ⟩
    · rintro ⟨x, hx, hψ⟩; exact ⟨x, Nat.le_of_lt hx, hx, hψ⟩

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.allV_support
#check_upstream ClassicalTheorems.Progress.Arithmetic.exists_bounded_lt
#check_upstream ClassicalTheorems.Progress.Arithmetic.exists_strict_bounded_quantifiers

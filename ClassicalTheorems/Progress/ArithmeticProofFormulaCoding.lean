/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofTokenCoding

/-! Effective partial inverse for sentence serialization. Recovering positive
and negative token lists together follows Foundation's finite dependency graph
for formulas, with bound arity increasing beneath quantifiers. -/

noncomputable section
open Classical Encodable FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

abbrev FormulaTokenPair := Option (List ℕ) × Option (List ℕ)

def originalFormulaTokens {k : ℕ} (φ : language.BoundedFormula Empty k) : List ℕ :=
  φ.listEncode.map encode

theorem original_tokens_falsum (k : ℕ) :
    originalFormulaTokens (.falsum : language.BoundedFormula Empty k) = [4 * k + 11] := by
  simp only [originalFormulaTokens, BoundedFormula.listEncode, List.map_cons, List.map_nil,
    encode_inr]
  change [2 * (2 * (k + 2) + 1) + 1] = _
  congr 1
  omega

theorem original_tokens_equal {k : ℕ} (t u : language.Term (Empty ⊕ Fin k)) :
    originalFormulaTokens (.equal t u) = [2 * Nat.pair k (encode t), 2 * Nat.pair k (encode u)] := rfl

theorem original_tokens_imp {k : ℕ} (φ ψ : language.BoundedFormula Empty k) :
    originalFormulaTokens (φ.imp ψ) = 3 :: (originalFormulaTokens φ ++ originalFormulaTokens ψ) := by
  simp [originalFormulaTokens, BoundedFormula.listEncode]

theorem original_tokens_all {k : ℕ} (φ : language.BoundedFormula Empty (k + 1)) :
    originalFormulaTokens φ.all = 7 :: originalFormulaTokens φ := rfl

def proofFormulaTokens {k : ℕ} (σ : FFL.FirstOrder.Semisentence proofLanguage k) : FormulaTokenPair :=
  ((fromProofFormula σ).1.map originalFormulaTokens,
    (fromProofFormula σ).2.map originalFormulaTokens)

def readProofFormulaTokens (b : ℕ × ℕ) : FormulaTokenPair :=
  ((decode₂ (FFL.FirstOrder.Semisentence proofLanguage b.1) b.2).map proofFormulaTokens).getD (none, none)

def proofAtomTokens (k : ℕ) (args : List ℕ) : List ℕ :=
  [2 * Nat.pair k (encode (readProofTermTokens k (args.getD 0 0))),
    2 * Nat.pair k (encode (readProofTermTokens k (args.getD 1 0)))]

def tokenImp (p q : Option (List ℕ)) : Option (List ℕ) :=
  p.bind (fun p => q.map (fun q => 3 :: (p ++ q)))

def tokenAll (p : Option (List ℕ)) : Option (List ℕ) := p.map (fun p => 7 :: p)

set_option maxHeartbeats 1000000 in
theorem primrec_tokenImp : Primrec₂ tokenImp := by
  unfold tokenImp
  primrec

theorem primrec_tokenAll : Primrec tokenAll := by
  unfold tokenAll
  exact Primrec.option_map₁ (Primrec.list_cons.comp (Primrec.const 7) Primrec.id)

def proofFormulaTokenStep (b : ℕ × ℕ) (vs : List FormulaTokenPair) : FormulaTokenPair :=
  let k := b.1
  let c := b.2
  let d := c - 1
  if encode (decode c : Option (FFL.FirstOrder.Semisentence proofLanguage k)) = c + 1 then
    if d.unpair.1 = 0 then
      (some (proofAtomTokens k (Nat.natToList d.unpair.2.unpair.2.unpair.2)), none)
    else if d.unpair.1 = 1 then
      (none, some (proofAtomTokens k (Nat.natToList d.unpair.2.unpair.2.unpair.2)))
    else if d.unpair.1 = 2 then (none, some [4 * k + 11])
    else if d.unpair.1 = 3 then (some [4 * k + 11], none)
    else if d.unpair.1 = 4 then
      (none, tokenImp (vs.getD 0 (none, none)).1 (vs.getD 1 (none, none)).2)
    else if d.unpair.1 = 5 then
      (tokenImp (vs.getD 0 (none, none)).2 (vs.getD 1 (none, none)).1, none)
    else if d.unpair.1 = 6 then
      (tokenAll (vs.getD 0 (none, none)).1, none)
    else if d.unpair.1 = 7 then
      (none, tokenAll (vs.getD 0 (none, none)).2)
    else (none, none)
  else (none, none)

set_option maxHeartbeats 2000000 in
theorem primrec_proofFormulaTokenStep : Primrec₂ proofFormulaTokenStep := by
  have hd := FFL.FirstOrder.Semiformula.encode_ofNat_primrec (L := proofLanguage) (ξ := Empty)
  have ha : Primrec₂ proofAtomTokens := by
    unfold proofAtomTokens
    have h0 : Primrec (fun p : ℕ × List ℕ => readProofTermTokens p.1 (p.2.getD 0 0)) :=
      primrec_readProofTermTokens.comp Primrec.fst (by primrec)
    have h1 : Primrec (fun p : ℕ × List ℕ => readProofTermTokens p.1 (p.2.getD 1 0)) :=
      primrec_readProofTermTokens.comp Primrec.fst (by primrec)
    primrec
  unfold proofFormulaTokenStep
  have hdecode : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      encode (decode p.1.2 : Option (FFL.FirstOrder.Semisentence proofLanguage p.1.1))) :=
    hd.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst)
  have hatom : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      proofAtomTokens p.1.1 ((p.1.2 - 1).unpair.2.unpair.2.unpair.2.natToList)) :=
    ha.comp (by primrec) (by primrec)
  have hi0 : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      tokenImp (p.2.getD 0 (none, none)).1 (p.2.getD 1 (none, none)).2) :=
    primrec_tokenImp.comp (by primrec) (by primrec)
  have hi1 : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      tokenImp (p.2.getD 0 (none, none)).2 (p.2.getD 1 (none, none)).1) :=
    primrec_tokenImp.comp (by primrec) (by primrec)
  have hall0 : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      tokenAll (p.2.getD 0 (none, none)).1) := primrec_tokenAll.comp (by primrec)
  have hall1 : Primrec (fun p : (ℕ × ℕ) × List FormulaTokenPair =>
      tokenAll (p.2.getD 0 (none, none)).2) := primrec_tokenAll.comp (by primrec)
  primrec

theorem readProofFormulaTokens_encode {k : ℕ} (σ : FFL.FirstOrder.Semisentence proofLanguage k) :
    readProofFormulaTokens (k, encode σ) = proofFormulaTokens σ := by
  simp [readProofFormulaTokens, decode₂_encode]

theorem proofAtomTokens_correct {k j : ℕ} (r : proofLanguage.Rel j)
    (ts : Fin j → FFL.FirstOrder.ClosedSemiterm proofLanguage k) :
    proofAtomTokens k (List.ofFn (fun i => encode (ts i))) =
      originalFormulaTokens (fromProofAtom r ts) := by
  have h := proof_relation_arity r
  subst j
  rw [Matrix.fun_eq_vec_two (fun i => encode (ts i))]
  simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, proofAtomTokens, List.getD_cons_zero, List.getD_cons_succ,
    readProofTermTokens_encode]
  unfold proofTermTokens fromProofAtom
  rw [original_tokens_equal, encode_list_map_encode, encode_list_map_encode]
  rfl

theorem proofFormulaTokenStep_valid {k : ℕ} (σ : FFL.FirstOrder.Semisentence proofLanguage k) :
    proofFormulaTokenStep (k, encode σ)
      ((FFL.FirstOrder.Semiformula.subArgs (k, encode σ)).map readProofFormulaTokens) =
        proofFormulaTokens σ := by
  unfold proofFormulaTokenStep
  dsimp only
  rw [encodek]
  simp only [encode_some, ite_true]
  cases σ with
  | verum => simp [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      proofFormulaTokens, fromProofFormula, original_tokens_falsum]
  | falsum => simp [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      proofFormulaTokens, fromProofFormula, original_tokens_falsum]
  | rel r ts =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair, ite_true]
    change (some (proofAtomTokens k (Matrix.vecToNat (fun i => encode (ts i))).natToList), none) = _
    rw [Nat.natToVec_eq_some_iff.mp (Nat.natToVec_vecToNat (fun i => encode (ts i))),
      proofAtomTokens_correct r ts]
    rfl
  | nrel r ts =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair, ite_true]
    change (none, some (proofAtomTokens k (Matrix.vecToNat (fun i => encode (ts i))).natToList)) = _
    rw [Nat.natToVec_eq_some_iff.mp (Nat.natToVec_vecToNat (fun i => encode (ts i))),
      proofAtomTokens_correct r ts]
    rfl
  | and φ ψ =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair]
    change (none, _) = _
    simp only [FFL.FirstOrder.Semiformula.subArgs, Nat.unpair_pair,
      ← FFL.FirstOrder.Semiformula.encode_eq_toNat]
    cases hφ : (fromProofFormula φ).1 <;> cases hψ : (fromProofFormula ψ).2 <;>
      simp [readProofFormulaTokens_encode, proofFormulaTokens, fromProofFormula, hφ, hψ, original_tokens_imp, tokenImp]
  | or φ ψ =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair]
    simp only [FFL.FirstOrder.Semiformula.subArgs, Nat.unpair_pair,
      ← FFL.FirstOrder.Semiformula.encode_eq_toNat]
    cases hφ : (fromProofFormula φ).2 <;> cases hψ : (fromProofFormula ψ).1 <;>
      simp [readProofFormulaTokens_encode, proofFormulaTokens, fromProofFormula, hφ, hψ, original_tokens_imp, tokenImp]
  | all φ =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair]
    simp only [FFL.FirstOrder.Semiformula.subArgs, Nat.unpair_pair,
      ← FFL.FirstOrder.Semiformula.encode_eq_toNat]
    cases hφ : (fromProofFormula φ).1 <;>
      simp [readProofFormulaTokens_encode, proofFormulaTokens, fromProofFormula, hφ, original_tokens_all, tokenAll]
  | exs φ =>
    simp only [FFL.FirstOrder.Semiformula.encode_eq_toNat, FFL.FirstOrder.Semiformula.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair]
    simp only [FFL.FirstOrder.Semiformula.subArgs, Nat.unpair_pair,
      ← FFL.FirstOrder.Semiformula.encode_eq_toNat]
    cases hφ : (fromProofFormula φ).2 <;>
      simp [readProofFormulaTokens_encode, proofFormulaTokens, fromProofFormula, hφ, original_tokens_all, tokenAll]

theorem proofFormulaTokenStep_correct (b : ℕ × ℕ) :
    proofFormulaTokenStep b ((FFL.FirstOrder.Semiformula.subArgs b).map readProofFormulaTokens) =
      readProofFormulaTokens b := by
  obtain ⟨k, c⟩ := b
  by_cases hc : encode (decode c : Option (FFL.FirstOrder.Semisentence proofLanguage k)) = c + 1
  · cases hd : (decode c : Option (FFL.FirstOrder.Semisentence proofLanguage k)) with
    | none => simp [hd] at hc
    | some σ =>
      have he : encode σ = c := by simpa [hd] using hc
      rw [← he, readProofFormulaTokens_encode]
      exact proofFormulaTokenStep_valid σ
  · have hn : decode₂ (FFL.FirstOrder.Semisentence proofLanguage k) c = none := by
      cases hd : (decode c : Option (FFL.FirstOrder.Semisentence proofLanguage k)) with
      | none => simp [decode₂, hd]
      | some σ =>
        have he : encode σ ≠ c := by simpa [hd] using hc
        simp [decode₂, hd, Option.guard, he]
    simp [proofFormulaTokenStep, hc, readProofFormulaTokens, hn]

theorem primrec_readProofFormulaTokens : Primrec readProofFormulaTokens :=
  Primrec.nat_omega_rec' readProofFormulaTokens
    (m := fun b => b.2) (l := FFL.FirstOrder.Semiformula.subArgs)
    (g := fun b vs => some (proofFormulaTokenStep b vs))
    Primrec.snd FFL.FirstOrder.Semiformula.primrec_subArgs
    (Primrec.option_some.comp primrec_proofFormulaTokenStep)
    FFL.FirstOrder.Semiformula.subArgs_ord
    (fun b => congrArg some (proofFormulaTokenStep_correct b))

def readOriginalSentenceCode (σ : FFL.FirstOrder.Sentence proofLanguage) : Option ℕ :=
  (readProofFormulaTokens (0, encode σ)).1.map encode

theorem primrec_readOriginalSentenceCode : Primrec readOriginalSentenceCode := by
  have h : Primrec (fun σ : FFL.FirstOrder.Sentence proofLanguage =>
      readProofFormulaTokens (0, encode σ)) := primrec_readProofFormulaTokens.comp
    (Primrec.pair (Primrec.const 0) Primrec.encode)
  unfold readOriginalSentenceCode
  exact Primrec.option_map (Primrec.fst.comp h)
    (Primrec.encode.comp (Primrec.snd : Primrec (fun p : FFL.FirstOrder.Sentence proofLanguage × List ℕ => p.2))).to₂

theorem readOriginalSentenceCode_eq (σ : FFL.FirstOrder.Sentence proofLanguage) :
    readOriginalSentenceCode σ = (fromProofFormula σ).1.map code := by
  rw [readOriginalSentenceCode, readProofFormulaTokens_encode]
  simp only [proofFormulaTokens, Option.map_map]
  congr 1
  funext φ
  exact encode_list_map_encode _

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_readProofFormulaTokens
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_readOriginalSentenceCode
#check_upstream ClassicalTheorems.Progress.Arithmetic.readOriginalSentenceCode_eq

/-
Copyright 2026 Michael Brackx
SPDX-License-Identifier: Apache-2.0
-/

import ClassicalTheorems.Progress.ArithmeticProofDecoder
import ClassicalTheorems.Progress.ArithmeticEffectiveSubstitution

/-! Primitive-recursive recovery of the original serialized tokens from
Foundation codes. The decoder accepts only canonical codes, so arbitrary
numeric inputs cannot masquerade as translated original formulas. -/

noncomputable section
open Classical Encodable FFL
open _root_.FirstOrder.Language
open ClassicalTheorems.Statements.Arithmetic
namespace ClassicalTheorems.Progress.Arithmetic

local instance proofTokenFunctionEncoding (j : ℕ) : Encodable (language.Functions j) :=
  FFL.FirstOrder.Language.Encodable.func (L := proofLanguage) j

def proofTermTokens {k : ℕ} (t : FFL.FirstOrder.ClosedSemiterm proofLanguage k) : List ℕ :=
  (fromProofTerm t).listEncode.map encode

def readProofTermTokens (k c : ℕ) : List ℕ :=
  ((decode₂ (FFL.FirstOrder.ClosedSemiterm proofLanguage k) c).map proofTermTokens).getD []

def proofTermTokenStep (k : ℕ) (table : List (List ℕ)) : List ℕ :=
  let c := table.length
  let d := c - 1
  if encode (decode c : Option (FFL.FirstOrder.ClosedSemiterm proofLanguage k)) = c + 1 then
    if d.unpair.1 = 0 then [4 * (k - 1 - d.unpair.2) + 2]
    else (2 * Nat.pair d.unpair.2.unpair.1 d.unpair.2.unpair.2.unpair.1 + 1) ::
      (Nat.natToList d.unpair.2.unpair.2.unpair.2).flatMap (fun j => table.getD j [])
  else []

set_option maxHeartbeats 2000000 in
theorem primrec_proofTermTokenStep : Primrec₂ proofTermTokenStep := by
  have hflat : Primrec (fun p : ℕ × List (List ℕ) =>
      (Nat.natToList (p.2.length - 1).unpair.2.unpair.2.unpair.2).flatMap
        (fun j => p.2.getD j [])) :=
    Primrec.list_flatMap (by primrec) (by primrec)
  have hdecode := FFL.FirstOrder.Semiterm.encode_ofNat_primrec
    (L := proofLanguage) (ξ := Empty)
  unfold proofTermTokenStep
  have hd : Primrec (fun p : ℕ × List (List ℕ) =>
      encode (decode p.2.length : Option (FFL.FirstOrder.ClosedSemiterm proofLanguage p.1))) :=
    hdecode.comp Primrec.fst (Primrec.list_length.comp Primrec.snd)
  primrec

theorem proof_term_code_child_lt {k j : ℕ} (f : proofLanguage.Func j)
    (ts : Fin j → FFL.FirstOrder.ClosedSemiterm proofLanguage k) (i : Fin j) :
    encode (ts i) < encode (FFL.FirstOrder.Semiterm.func f ts) := by
  have h := Nat.lt_of_eq_natToVec
    (Nat.natToVec_vecToNat (fun i => encode (ts i))) i
  change encode (ts i) < Nat.pair 2 (Nat.pair j (Nat.pair (encode f)
    (Matrix.vecToNat (fun i => encode (ts i))))) + 1
  have h1 := Nat.right_le_pair (encode f) (Matrix.vecToNat (fun i => encode (ts i)))
  have h2 := Nat.right_le_pair j (Nat.pair (encode f) (Matrix.vecToNat (fun i => encode (ts i))))
  have h3 := Nat.right_le_pair 2 (Nat.pair j
    (Nat.pair (encode f) (Matrix.vecToNat (fun i => encode (ts i)))))
  omega

theorem readProofTermTokens_encode {k : ℕ} (t : FFL.FirstOrder.ClosedSemiterm proofLanguage k) :
    readProofTermTokens k (encode t) = proofTermTokens t := by
  simp [readProofTermTokens, decode₂_encode]

theorem proofTermTokenStep_valid {k : ℕ} (t : FFL.FirstOrder.ClosedSemiterm proofLanguage k)
    (table : List (List ℕ)) (hlen : table.length = encode t)
    (hentries : ∀ j < encode t, table.getD j [] = readProofTermTokens k j) :
    proofTermTokenStep k table = proofTermTokens t := by
  unfold proofTermTokenStep
  dsimp only
  rw [hlen, encodek]
  simp only [encode_some, ite_true]
  cases t with
  | bvar i =>
    simp only [FFL.FirstOrder.Semiterm.encode_eq_toNat, FFL.FirstOrder.Semiterm.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair]
    change [4 * (k - 1 - i.val) + 2] =
      (Term.listEncode (Term.var (Sum.inr i.rev : Empty ⊕ Fin k))).map encode
    simp only [Term.listEncode, List.map_cons, List.map_nil, encode_inl, encode_inr]
    change [4 * (k - 1 - i.val) + 2] = [2 * (2 * i.rev.val + 1)]
    simp only [Fin.val_rev]
    congr 1
    omega
  | fvar a => exact Empty.elim a
  | @func j f ts =>
    simp only [FFL.FirstOrder.Semiterm.encode_eq_toNat, FFL.FirstOrder.Semiterm.toNat,
      Nat.add_sub_cancel, Nat.unpair_pair, ite_eq_right (by decide : ¬(2 : ℕ) = 0)]
    change (2 * Nat.pair j (encode f) + 1) ::
      (Matrix.vecToNat (fun i => encode (ts i))).natToList.flatMap (fun j => table.getD j []) = _
    have hl := Nat.natToVec_eq_some_iff.mp
      (Nat.natToVec_vecToNat (fun i => encode (ts i)))
    rw [hl, List.ofFn_eq_map, List.flatMap_map]
    unfold proofTermTokens fromProofTerm
    simp only [Term.listEncode, List.map_cons, List.map_flatMap, encode_inr]
    congr 1
    have hg (i : Fin j) : table.getD (encode (ts i)) [] =
        (fromProofTerm (ts i)).listEncode.map encode := by
      rw [hentries _ (proof_term_code_child_lt f ts i), readProofTermTokens_encode]
      rfl
    simpa [List.ofFn_eq_map, Function.comp_def] using congrArg
      (fun g : Fin j → List ℕ => (List.finRange j).flatMap g) (funext hg)

theorem proofTermTokenStep_correct (k c : ℕ) :
    proofTermTokenStep k ((List.range c).map (readProofTermTokens k)) = readProofTermTokens k c := by
  have hlen : ((List.range c).map (readProofTermTokens k)).length = c := by simp
  by_cases hc : encode (decode c : Option (FFL.FirstOrder.ClosedSemiterm proofLanguage k)) = c + 1
  · cases hd : (decode c : Option (FFL.FirstOrder.ClosedSemiterm proofLanguage k)) with
    | none => simp [hd] at hc
    | some t =>
      have he : encode t = c := by simpa [hd] using hc
      rw [← he]
      rw [readProofTermTokens_encode]
      apply proofTermTokenStep_valid t _ (by simp)
      intro j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      rfl
  · have hn : decode₂ (FFL.FirstOrder.ClosedSemiterm proofLanguage k) c = none := by
      cases hd : (decode c : Option (FFL.FirstOrder.ClosedSemiterm proofLanguage k)) with
      | none => simp [decode₂, hd]
      | some t =>
        have he : encode t ≠ c := by simpa [hd] using hc
        simp [decode₂, hd, Option.guard, he]
    simp [proofTermTokenStep, hlen, hc, readProofTermTokens, hn]

theorem primrec_readProofTermTokens : Primrec₂ readProofTermTokens :=
  Primrec.nat_strong_rec readProofTermTokens
    (g := fun k table => some (proofTermTokenStep k table))
    (Primrec.option_some.comp primrec_proofTermTokenStep)
    (fun k c => congrArg some (proofTermTokenStep_correct k c))

end ClassicalTheorems.Progress.Arithmetic
#check_upstream ClassicalTheorems.Progress.Arithmetic.primrec_readProofTermTokens

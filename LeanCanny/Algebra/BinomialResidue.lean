/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinomialPower

/-!
# A certified space-bounded binomial residue evaluator

Input `pair n (pair k b)` contains little-endian words and specifies modulus
`fromBitsLE b + 1`. All words, including noncanonical ones, are accepted. A
uniform FP accessor supplies the bidiagonal matrix entries. The streamed power
controller returns the complete residue of `choose n k`, with polynomial-length
states and an exponential clock in the input length.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinomialResidue
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

def nWord : List Bool → List Bool := pairFst
def kWord (c : List Bool) : List Bool := pairFst (pairSnd c)
def mWord (c : List Bool) : List Bool := pairSnd (pairSnd c)
def dimension (c : List Bool) : List Bool := BinaryNat.succ (kWord c)
def modulus (c : List Bool) : List Bool := BinaryNat.succ (mWord c)
def exponent (c : List Bool) : List Bool := BinaryNat.normalize (nWord c)
def row (c : List Bool) : List Bool := BinaryNat.normalize (kWord c)
def rowIndex (p : List Bool) : List Bool := pairFst (pairSnd p)
def colIndex (p : List Bool) : List Bool := pairSnd (pairSnd p)

def entry (p : List Bool) : List Bool :=
  if rowIndex p = colIndex p ∨ rowIndex p = BinaryNat.succ (colIndex p)
  then ArithmeticBits.one (modulus (pairFst p)) else []

def family : ModularFamily where
  dimension := fun c => Nat.fromBitsLE (kWord c) + 1
  modulus := fun c => Nat.fromBitsLE (mWord c) + 1
  exponent := fun c => Nat.fromBitsLE (nWord c)
  row := fun c => Fin.last (Nat.fromBitsLE (kWord c))
  col := fun _ => 0
  matrix := fun c => BinomialPower.matrix (Nat.fromBitsLE (kWord c))
  modulus_ne_zero := fun _ => by omega

def value (c : List Bool) : List Bool :=
  BinaryNatCode.encode ((Nat.fromBitsLE (nWord c)).choose (Nat.fromBitsLE (kWord c)) %
    (Nat.fromBitsLE (mWord c) + 1))

theorem nWord_mem_FP : nWord ∈ FP := pairFst_mem_FP
theorem kWord_mem_FP : kWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem mWord_mem_FP : mWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem dimension_mem_FP : dimension ∈ FP := by
  have h := mem_FP_comp kWord_mem_FP BinaryNat.succ_mem_FP
  exact h

theorem modulus_mem_FP : modulus ∈ FP := by
  have h := mem_FP_comp mWord_mem_FP BinaryNat.succ_mem_FP
  exact h

theorem exponent_mem_FP : exponent ∈ FP := by
  have h := mem_FP_comp nWord_mem_FP BinaryNat.normalize_mem_FP
  exact h

theorem row_mem_FP : row ∈ FP := by
  have h := mem_FP_comp kWord_mem_FP BinaryNat.normalize_mem_FP
  exact h

theorem rowIndex_mem_FP : rowIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem colIndex_mem_FP : colIndex ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP

theorem entry_mem_FP : entry ∈ FP := by
  have hd := stringEq_fppred rowIndex_mem_FP colIndex_mem_FP
  have hs := stringEq_fppred rowIndex_mem_FP (mem_FP_comp colIndex_mem_FP BinaryNat.succ_mem_FP)
  have ho := mem_FP_comp (mem_FP_comp pairFst_mem_FP modulus_mem_FP) ArithmeticBits.one_mem_FP
  have h := (hd.or hs).ite_mem_FP ho (constFn_mem_FP [])
  refine mem_FP_of_eq (g := entry) h ?_
  intro p
  simp only [Function.comp_apply, entry]

theorem succ_code (k : ℕ) : BinaryNat.succ (BinaryNatCode.encode k) = BinaryNatCode.encode (k + 1) := by
  simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem modulus_code (c : List Bool) : modulus c = BinaryNatCode.encode (family.modulus c) := by
  simp only [modulus, family, BinaryNat.succ_eq_bits, BinaryNatCode.encode]

def access : ModularAccess family where
  dimension := dimension
  modulus := modulus
  exponent := exponent
  row := row
  col := fun _ => []
  entry := entry
  dimension_eq := fun c => by simp only [dimension, family, BinaryNat.succ_eq_bits, BinaryNatCode.encode]
  modulus_eq := modulus_code
  exponent_eq := fun c => by simp only [exponent, family, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  row_eq := fun c => by simp only [row, family, Fin.val_last, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]
  col_eq := fun _ => rfl
  entry_eq := by
    intro c i j
    change Fin (Nat.fromBitsLE (kWord c) + 1) at i j
    let : NeZero (family.modulus c) := ⟨family.modulus_ne_zero c⟩
    change entry (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits (BinomialPower.matrix (R := ZMod (family.modulus c)) (Nat.fromBitsLE (kWord c)) i j)
    rw [BinomialPower.matrix_apply (R := ZMod (family.modulus c))]
    simp only [entry, rowIndex, colIndex, pairFst_pair, pairSnd_pair, succ_code,
      BinaryNatCode.encode_injective.eq_iff]
    by_cases h : i.val = j.val ∨ i.val = j.val + 1
    · simp only [h, ↓reduceIte, modulus_code]
      exact ArithmeticBits.one_residueBits (family.modulus c)
    · simp only [h, ↓reduceIte]
      simp [residueBits, BinaryNatCode.encode]

theorem access_polyTime : access.PolyTime := by
  constructor
  · simpa only [access] using dimension_mem_FP
  · simpa only [access] using modulus_mem_FP
  · simpa only [access] using exponent_mem_FP
  · simpa only [access] using row_mem_FP
  · exact constFn_mem_FP []
  · simpa only [access] using entry_mem_FP

theorem family_value (c : List Bool) : family.value c = value c := by
  let : NeZero (family.modulus c) := ⟨family.modulus_ne_zero c⟩
  change residueBits ((BinomialPower.matrix (R := ZMod (family.modulus c))
    (Nat.fromBitsLE (kWord c)) ^ Nat.fromBitsLE (nWord c)) (Fin.last _) 0) = _
  rw [BinomialPower.pow_last_zero]
  change BinaryNatCode.encode
    ((↑((Nat.fromBitsLE (nWord c)).choose (Nat.fromBitsLE (kWord c))) :
      ZMod (Nat.fromBitsLE (mWord c) + 1)).val) = _
  rw [ZMod.val_natCast]
  rfl

theorem evaluator : SpaceFunction value := by
  rw [← show family.value = value from funext family_value]
  exact ModularAccess.evaluator access access_polyTime

theorem value_packet (n k b : ℕ) :
    value (pair (BinaryNatCode.encode n)
      (pair (BinaryNatCode.encode k) (BinaryNatCode.encode b))) =
        BinaryNatCode.encode (n.choose k % (b + 1)) := by
  simp only [value, nWord, kWord, mWord, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

def zeroLanguage : Language :=
  {c | (Nat.fromBitsLE (nWord c)).choose (Nat.fromBitsLE (kWord c)) %
    (Nat.fromBitsLE (mWord c) + 1) = 0}

theorem zeroLanguage_mem_PSPACE : zeroLanguage ∈ PSPACE := by
  let accept := fun bits : List Bool => decide (bits = [])
  have ha : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply (evaluator.decider accept ha ?_).mem_PSPACE
  intro c
  change _ ↔ decide (value c = []) = true
  simp only [decide_eq_true_eq, value, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  rfl

end LeanCanny.Algebra.BinomialResidue

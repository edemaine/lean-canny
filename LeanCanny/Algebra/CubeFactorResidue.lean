/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CubeFactorCoefficients
public import LeanCanny.Algebra.BinomialResidue
public import LeanCanny.Algebra.ModularNegFP
public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Encoding.BinaryPowModFP
public import LeanCanny.Computation.SpaceFunctionChain

/-! # Polynomial-space residues of compactification factors

Input `pair e (pair s (pair k b))` requests the coefficient of X^k in
X^e*(1-X²)^s modulo `fromBitsLE b+1`. A binomial residue child and FP modular
arithmetic implement the coefficient formula on every binary input.
-/

@[expose] public section

namespace LeanCanny.Algebra.CubeFactorResidue
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower

-- Use the binary arithmetic specifications without unfolding their machines.
attribute [local irreducible] BinaryNat.succ BinaryNat.sub BinaryNat.half BinaryNat.mod
  BinaryNat.mulMod BinaryNat.powMod ArithmeticBits.one ArithmeticBits.negate BinomialResidue.value

def eWord : List Bool → List Bool := pairFst
def sWord (q : List Bool) : List Bool := pairFst (pairSnd q)
def kWord (q : List Bool) : List Bool := pairFst (pairSnd (pairSnd q))
def mWord (q : List Bool) : List Bool := pairSnd (pairSnd (pairSnd q))
def modulus (q : List Bool) : List Bool := BinaryNat.succ (mWord q)
def difference (q : List Bool) : List Bool := BinaryNat.sub (pair (kWord q) (eWord q))
def index (q : List Bool) : List Bool := BinaryNat.half (difference q)
def binomialQuery (q : List Bool) : List Bool := pair (sWord q) (pair (index q) (mWord q))
def negativeOne (q : List Bool) : List Bool := ArithmeticBits.negate (pair (modulus q) (ArithmeticBits.one (modulus q)))
def powerQuery (q : List Bool) : List Bool := pair (negativeOne q) (pair (index q) (mWord q))
def admissible (q : List Bool) : Prop :=
  Nat.fromBitsLE (eWord q) ≤ Nat.fromBitsLE (kWord q) ∧ 2 ∣ Nat.fromBitsLE (kWord q) - Nat.fromBitsLE (eWord q)
instance (q : List Bool) : Decidable (admissible q) := inferInstanceAs (Decidable (_ ∧ _))

def finish (z : List Bool) : List Bool :=
  if admissible (pairFst z) then BinaryNat.mulMod (pair (modulus (pairFst z))
    (pair (pairSnd z) (BinaryNat.powMod (powerQuery (pairFst z))))) else []
def computed (q : List Bool) : List Bool := finish (pair q (BinomialResidue.value (binomialQuery q)))

theorem eWord_mem_FP : eWord ∈ FP := pairFst_mem_FP
theorem sWord_mem_FP : sWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem kWord_mem_FP : kWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem mWord_mem_FP : mWord ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem modulus_mem_FP : modulus ∈ FP := by
  have h := mem_FP_comp mWord_mem_FP BinaryNat.succ_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)
theorem difference_mem_FP : difference ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair kWord_mem_FP eWord_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)
theorem index_mem_FP : index ∈ FP := by
  have h := mem_FP_comp difference_mem_FP BinaryNat.half_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)
theorem binomialQuery_mem_FP : binomialQuery ∈ FP := by
  have h := mem_FP_pair sWord_mem_FP (mem_FP_pair index_mem_FP mWord_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem negativeOne_mem_FP : negativeOne ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair modulus_mem_FP (mem_FP_comp modulus_mem_FP ArithmeticBits.one_mem_FP))
    ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)
theorem powerQuery_mem_FP : powerQuery ∈ FP := by
  have h := mem_FP_pair negativeOne_mem_FP (mem_FP_pair index_mem_FP mWord_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem admissible_fppred : FPPred admissible := by
  have hm := mem_FP_comp (mem_FP_pair difference_mem_FP (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.mod_mem_FP
  apply ((BinaryNat.le_fppred eWord_mem_FP kWord_mem_FP).and (stringEq_fppred hm (constFn_mem_FP []))).of_iff
  intro q
  simp only [Function.comp_apply, BinaryNat.mod_pair, difference, BinaryNat.sub_pair, Nat.fromBitsLE_bits,
    BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff, Nat.dvd_iff_mod_eq_zero, admissible]

theorem finish_mem_FP : finish ∈ FP := by
  have hp := mem_FP_comp (mem_FP_comp pairFst_mem_FP powerQuery_mem_FP) BinaryNat.powMod_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP modulus_mem_FP
  have hv := mem_FP_comp (mem_FP_pair hm (mem_FP_pair pairSnd_mem_FP hp)) BinaryNat.mulMod_mem_FP
  have h := (admissible_fppred.comp pairFst_mem_FP).ite_mem_FP hv (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

theorem evaluator : SpaceFunction computed := by
  let E := (BinomialResidue.evaluator.precompose binomialQuery binomialQuery_mem_FP).withInput.postcompose finish finish_mem_FP
  exact E.congr (funext fun _ => rfl)

def mValue (q : List Bool) : ℕ := Nat.fromBitsLE (mWord q) + 1
def hValue (q : List Bool) : ℕ := (Nat.fromBitsLE (kWord q) - Nat.fromBitsLE (eWord q)) / 2

theorem modulus_code (q : List Bool) : modulus q = BinaryNatCode.encode (mValue q) := by
  simp only [modulus, mValue, BinaryNat.succ_eq_bits, BinaryNatCode.encode]
theorem index_code (q : List Bool) : index q = BinaryNatCode.encode (hValue q) := by
  simp only [index, difference, hValue, BinaryNat.half_eq_bits, BinaryNat.sub_pair,
    Nat.fromBitsLE_bits, BinaryNatCode.encode]

theorem binomial_correct (q : List Bool) : BinomialResidue.value (binomialQuery q) =
    residueBits (((Nat.fromBitsLE (sWord q)).choose (hValue q) : ℕ) : ZMod (mValue q)) := by
  rw [show residueBits (((Nat.fromBitsLE (sWord q)).choose (hValue q) : ℕ) : ZMod (mValue q)) =
    BinaryNatCode.encode ((Nat.fromBitsLE (sWord q)).choose (hValue q) % mValue q) from
      congrArg BinaryNatCode.encode (ZMod.val_natCast _ _)]
  simp only [BinomialResidue.value, binomialQuery, BinomialResidue.nWord, BinomialResidue.kWord,
    BinomialResidue.mWord, pairFst_pair, pairSnd_pair, index_code, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    mValue]

theorem power_correct (q : List Bool) : BinaryNat.powMod (powerQuery q) = residueBits ((-1 : ZMod (mValue q)) ^ hValue q) := by
  let : NeZero (mValue q) := ⟨by simp [mValue]⟩
  have hn : negativeOne q = residueBits (-1 : ZMod (mValue q)) := by
    rw [negativeOne, modulus_code, ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]
  unfold mValue at hn ⊢
  rw [powerQuery, hn, index_code]
  have h := ArithmeticBits.powMod_residueBits (mWord q) (BinaryNatCode.encode (hValue q)) (-1)
  simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using h

theorem computed_correct (q : List Bool) : computed q = residueBits
    (((CubeFactor.polynomial (R := ℤ) (Nat.fromBitsLE (eWord q)) (Nat.fromBitsLE (sWord q))).coeff
      (Nat.fromBitsLE (kWord q)) : ℤ) : ZMod (mValue q)) := by
  let : NeZero (mValue q) := ⟨by simp [mValue]⟩
  rw [computed, finish, pairFst_pair, pairSnd_pair, CubeFactor.coeff]
  change (if admissible q then _ else []) = residueBits ((if admissible q then _ else 0 : ℤ) : ZMod (mValue q))
  by_cases h : admissible q
  · rw [ite_eq_left h, ite_eq_left h, modulus_code, binomial_correct, power_correct, ArithmeticBits.mulMod_residueBits]
    simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one, hValue]
  · rw [ite_eq_right h, ite_eq_right h]
    simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.CubeFactorResidue

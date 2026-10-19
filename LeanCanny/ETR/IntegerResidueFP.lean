/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.NumericPayloadFP
public import LeanCanny.Algebra.ModularNegFP

/-!
# FP residue evaluation for encoded integer constants

The packet pairs the original integer payload with a binary modulus. Negative
payloads store `n` for `-(n+1)`, so evaluation increments the magnitude before
modular negation. The result agrees with integer casting into every positive
modulus, including modulus one, without constructing a unary magnitude.
-/

@[expose] public section

namespace LeanCanny.ETR.Codec.IntegerResidue
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Algebra.MatrixPower

noncomputable def residue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

def naturalDigits (bits : List Bool) : List Bool := (BitPayload.run (contents bits)).output
def magnitudeDigits (bits : List Bool) : List Bool := naturalDigits (integerMagnitude bits)
def negative (bits : List Bool) : Prop := firstChild bits = (unary 1).toBits
instance (bits : List Bool) : Decidable (negative bits) := inferInstanceAs (Decidable (_ = _))

theorem naturalDigits_mem_FP : naturalDigits ∈ FP := by
  have h := mem_FP_comp contents_mem_FP BitPayload.output_mem_FP
  exact mem_FP_of_eq (g := naturalDigits) h (fun _ => rfl)

theorem magnitudeDigits_mem_FP : magnitudeDigits ∈ FP := by
  have h := mem_FP_comp integerMagnitude_mem_FP naturalDigits_mem_FP
  exact mem_FP_of_eq (g := magnitudeDigits) h (fun _ => rfl)

theorem negative_fppred : FPPred negative := stringEq_fppred firstChild_mem_FP (constFn_mem_FP (unary 1).toBits)

theorem naturalDigits_natural (n : ℕ) : naturalDigits (natural n).toBits = BinaryNatCode.encode n := by
  simp only [naturalDigits, natural, contents_toBits, List.map_map, Function.comp_def]
  change (BitPayload.run (BitPayload.body n.bits)).output = _
  rw [BitPayload.run_body]
  rfl

theorem magnitudeDigits_ofNat (n : ℕ) : magnitudeDigits (integer (Int.ofNat n)).toBits = BinaryNatCode.encode n := by
  simp only [magnitudeDigits, integerMagnitude, integer, remainingChildren_toBits, firstChild_toBits, naturalDigits_natural]

theorem magnitudeDigits_negSucc (n : ℕ) : magnitudeDigits (integer (Int.negSucc n)).toBits = BinaryNatCode.encode n := by
  simp only [magnitudeDigits, integerMagnitude, integer, remainingChildren_toBits, firstChild_toBits, naturalDigits_natural]

def value (p : List Bool) : List Bool :=
  if negative (pairFst p) then
    ArithmeticBits.negate (pair (pairSnd p)
      (BinaryNat.mod (pair (BinaryNat.succ (magnitudeDigits (pairFst p))) (pairSnd p))))
  else BinaryNat.mod (pair (magnitudeDigits (pairFst p)) (pairSnd p))

theorem value_mem_FP : value ∈ FP := by
  have hmag := mem_FP_comp pairFst_mem_FP magnitudeDigits_mem_FP
  have hsucc := mem_FP_comp hmag BinaryNat.succ_mem_FP
  have hnegMod := mem_FP_comp (mem_FP_pair hsucc pairSnd_mem_FP) BinaryNat.mod_mem_FP
  have hneg := mem_FP_comp (mem_FP_pair pairSnd_mem_FP hnegMod) ArithmeticBits.negate_mem_FP
  have hpos := mem_FP_comp (mem_FP_pair hmag pairSnd_mem_FP) BinaryNat.mod_mem_FP
  have h := (negative_fppred.comp pairFst_mem_FP).ite_mem_FP hneg hpos
  refine mem_FP_of_eq (g := value) h ?_
  intro p
  simp only [value, Function.comp_apply]

theorem mod_nat_code (n m : ℕ) : BinaryNat.mod (pair (BinaryNatCode.encode n) (BinaryNatCode.encode m)) =
    residueBits (n : ZMod m) := by
  simp only [BinaryNat.mod_pair, residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_natCast]

theorem value_integer (z : ℤ) (m : ℕ) [NeZero m] :
    value (pair (integer z).toBits (BinaryNatCode.encode m)) = residueBits (z : ZMod m) := by
  cases z with
  | ofNat n =>
    have hneg : ¬ negative (integer (Int.ofNat n)).toBits := by
      simp [negative, integer, firstChild_toBits, Data.toBits_injective.eq_iff, unary]
    simp only [value, pairFst_pair, pairSnd_pair, hneg, ↓reduceIte, magnitudeDigits_ofNat, mod_nat_code]
    change residueBits (n : ZMod m) = residueBits ((n : ℤ) : ZMod m)
    rw [Int.cast_natCast]
  | negSucc n =>
    have hneg : negative (integer (Int.negSucc n)).toBits := by
      simp only [negative, integer, firstChild_toBits]
    simp only [value, pairFst_pair, pairSnd_pair, hneg, ↓reduceIte, magnitudeDigits_negSucc, BinaryNat.succ_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
    have hmod := mod_nat_code (n + 1) m
    simp only [BinaryNatCode.encode] at hmod
    rw [hmod]
    have hnegate := ArithmeticBits.negate_residueBits m ((n + 1 : ℕ) : ZMod m)
    simp only [BinaryNatCode.encode] at hnegate
    rw [hnegate]
    simp only [Int.cast_negSucc]

end LeanCanny.ETR.Codec.IntegerResidue

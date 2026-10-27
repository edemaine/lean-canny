/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerSumSpace

/-! # Canonical signed integer subtraction in native polynomial time -/

@[expose] public section
namespace LeanCanny.Algebra.SignedIntegerArithmetic
open LeanCanny.Encoding LeanCanny.Computation

def value (w : List Bool) : ℤ := (Nat.fromBitsLE (pairFst w) : ℤ) - Nat.fromBitsLE (pairSnd w)
def canonical (w : List Bool) : List Bool := IntegerSumBits.difference w
theorem canonical_FP : canonical ∈ FP := IntegerSumBits.difference_mem_FP
theorem canonical_eq (w : List Bool) : canonical w = SignStatisticBits.integerCode (value w) := by
  simp only [canonical, value, IntegerSumBits.difference, SignStatisticBits.integerCode,
    BinaryNat.sub_pair, BinaryNatCode.encode]
  congr 2 <;> omega

theorem value_packet (z : ℤ) : value (SignStatisticBits.integerCode z) = z := by
  simp only [value, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

theorem value_bound (w : List Bool) : (value w).natAbs < 2 ^ w.length := by
  have hp := (Nat.fromBitsLE_lt_pow_length (pairFst w)).trans_le
    (Nat.pow_le_pow_right (by decide) (pairFst_length_le w))
  have hn := (Nat.fromBitsLE_lt_pow_length (pairSnd w)).trans_le
    (Nat.pow_le_pow_right (by decide) (pairSnd_length_le w))
  unfold value
  omega

def subtract (w : List Bool) : List Bool := IntegerSumBits.difference (pair
  (BinaryNat.add (pair (pairFst (pairFst w)) (pairSnd (pairSnd w))))
  (BinaryNat.add (pair (pairSnd (pairFst w)) (pairFst (pairSnd w)))))

theorem subtract_FP : subtract ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hb := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hc := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hd := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hp := mem_FP_comp (mem_FP_pair ha hd) BinaryNat.add_mem_FP
  have hn := mem_FP_comp (mem_FP_pair hb hc) BinaryNat.add_mem_FP
  have H := mem_FP_comp (mem_FP_pair hp hn) IntegerSumBits.difference_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [subtract, Function.comp_apply])

theorem subtract_packet (x y : ℤ) : subtract (pair (SignStatisticBits.integerCode x) (SignStatisticBits.integerCode y)) =
    SignStatisticBits.integerCode (x - y) := by
  have hx : (x.toNat : ℤ) - (-x).toNat = x := by omega
  have hy : (y.toNat : ℤ) - (-y).toNat = y := by omega
  simp only [subtract, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change IntegerSumBits.difference (pair
    (BinaryNatCode.encode (x.toNat + (-y).toNat)) (BinaryNatCode.encode ((-x).toNat + y.toNat))) = _
  rw [IntegerSumBits.difference_parts]
  apply congrArg SignStatisticBits.integerCode
  simp only [Nat.cast_add]
  omega

end LeanCanny.Algebra.SignedIntegerArithmetic

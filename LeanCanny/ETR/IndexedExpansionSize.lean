/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.IndexedExpansionBounds

/-! # Literal input-size budgets for indexed expression coefficients -/

@[expose] public section

namespace LeanCanny.ETR
open Complexity

theorem Codec.bits_length_le_size (bits : List Bool) :
    bits.length ≤ (Data.l (bits.map Codec.bit)).size := by
  induction bits with
  | nil => simp
  | cons b bits ih =>
    cases b <;> simp only [List.map_cons, List.length_cons, Data.cons_size, Codec.bit,
      Bool.false_eq_true, ite_false, ite_true, Data.size_empty] <;> omega

theorem Codec.natural_bitSize_le_size (n : ℕ) : n.size ≤ (Codec.natural n).size := by
  simpa only [Codec.natural, Nat.size_eq_bits_len] using Codec.bits_length_le_size n.bits

theorem Codec.integer_natAbs_bitSize_le_size (z : ℤ) : z.natAbs.size ≤ (Codec.integer z).size := by
  cases z with
  | ofNat n =>
    have hn := Codec.natural_bitSize_le_size n
    change n.size ≤ _
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega
  | negSucc n =>
    have hn := Codec.natural_bitSize_le_size n
    have hsucc : (n + 1).size ≤ n.size + 1 := by
      apply Nat.size_le.mpr
      rw [pow_succ]
      have hlt := Nat.lt_size_self n
      have hpos : 0 < 2 ^ n.size := by positivity
      omega
    change (n + 1).size ≤ _
    simp only [Codec.integer, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega

theorem Term.indexedCoefficientBits_le_dataSize (t : Term) : t.indexedCoefficientBits ≤ t.toData.size := by
  induction t with
  | const z =>
    have hz := Codec.integer_natAbs_bitSize_le_size z
    simp only [Term.indexedCoefficientBits, Term.toData, Data.cons_size, Codec.unary_size, Data.size_empty]
    omega
  | var i => exact Nat.zero_le _
  | add a b ha hb => simp only [Term.indexedCoefficientBits, Term.dataSize_add]; omega
  | mul a b ha hb => simp only [Term.indexedCoefficientBits, Term.dataSize_mul]; omega

theorem Term.monomialCoefficient_natAbs_le_pow_dataSize (t : Term) (r : ℕ) :
    (t.monomialCoefficient r).natAbs ≤ 2 ^ t.toData.size :=
  (t.monomialCoefficient_natAbs_le r).trans (Nat.pow_le_pow_right (by decide) t.indexedCoefficientBits_le_dataSize)

end LeanCanny.ETR

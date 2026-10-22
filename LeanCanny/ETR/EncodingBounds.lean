/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Encoding

/-!
# Size bounds for the ETR encoding

Unary variable names ensure that a formula's arity is bounded by its literal input bit length.
Thus a binary input cannot request an exponentially long dense assignment merely by naming
a very large variable. Integer constants retain their binary encoding.
-/

@[expose] public section

namespace LeanCanny.ETR


@[simp] theorem Codec.unary_size (n : ℕ) : (Codec.unary n).size = 2 * n + 2 := by
  induction n with
  | zero =>
      simpa only [Codec.unary, List.replicate_zero, Nat.mul_zero, Nat.zero_add]
        using Data.size_empty
  | succ n ih =>
      simp only [Codec.unary, List.replicate_succ, Data.cons_size, Data.size_empty] at *
      omega

/-- Each binary digit in a natural-number payload uses at most four bracket bits. -/
theorem Codec.bits_size_le (bits : List Bool) :
    (Data.l (bits.map Codec.bit)).size ≤ 4 * bits.length + 2 := by
  induction bits with
  | nil => simp only [List.map_nil, Data.size_empty, List.length_nil, Nat.mul_zero, Nat.zero_add,
      Nat.le_refl]
  | cons b bs ih =>
      cases b <;> simp only [List.map_cons, Data.cons_size, Codec.bit, Bool.false_eq_true,
        ite_false, ite_true, Data.size_empty, List.length_cons] <;> omega

theorem Codec.natural_size_le (n : ℕ) : (Codec.natural n).size ≤ 4 * n.size + 2 := by
  simpa only [Codec.natural, Nat.size_eq_bits_len] using Codec.bits_size_le n.bits

theorem Term.arity_le_dataSize (t : Term) : t.arity ≤ t.toData.size := by
  induction t with
  | const z => exact Nat.zero_le _
  | var i =>
      simp only [Term.arity, Term.toData, Data.cons_size, Codec.unary_size, Data.size_empty]
      omega
  | add a b ha hb =>
      simp only [Term.arity, Term.toData, Data.cons_size, Codec.unary_size, Data.size_empty]
      omega
  | mul a b ha hb =>
      simp only [Term.arity, Term.toData, Data.cons_size, Codec.unary_size, Data.size_empty]
      omega

theorem Formula.arity_le_dataSize (p : Formula) : p.arity ≤ p.toData.size := by
  induction p with
  | falsum => exact Nat.zero_le _
  | eqZero t =>
      have := t.arity_le_dataSize
      simp only [Formula.arity, Formula.toData, Data.cons_size, Codec.unary_size,
        Data.size_empty]
      omega
  | ltZero t =>
      have := t.arity_le_dataSize
      simp only [Formula.arity, Formula.toData, Data.cons_size, Codec.unary_size,
        Data.size_empty]
      omega
  | not p hp =>
      simp only [Formula.arity, Formula.toData, Data.cons_size, Codec.unary_size,
        Data.size_empty]
      omega
  | and p q hp hq =>
      simp only [Formula.arity, Formula.toData, Data.cons_size, Codec.unary_size,
        Data.size_empty]
      omega
  | or p q hp hq =>
      simp only [Formula.arity, Formula.toData, Data.cons_size, Codec.unary_size,
        Data.size_empty]
      omega

/-- The number of variables in the finite existential block is at most the input length. -/
theorem Formula.arity_le_inputSize (p : Formula) : p.arity ≤ p.inputSize := by
  rw [Formula.inputSize_eq_dataSize]
  exact p.arity_le_dataSize

end LeanCanny.ETR

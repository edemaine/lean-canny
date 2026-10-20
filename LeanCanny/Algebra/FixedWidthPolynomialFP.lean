/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomial

/-! # FP metadata for dense indexed polynomial sources

The term count is exponential, but its binary word has A*W+1 bits. Coordinate
queries retain ranks and variable indices in binary. The bounded block reader
caps invalid variable indices before any unary conversion.
-/

@[expose] public section

namespace LeanCanny.Algebra.FixedWidthPolynomial
open Complexity
open LeanCanny.Encoding

def countCode (A W : List Bool → ℕ) (c : List Bool) : List Bool :=
  BinaryNat.normalize ((true :: List.replicate (A c * W c) false).reverse)

theorem countCode_mem_FP {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : countCode A W ∈ FP := by
  have hr := (hA.mul hW).replicate_mem_FP false
  have h := mem_FP_comp (mem_FP_comp (mem_FP_comp hr (Cobham.cons_mem_FP true)) reverse_mem_FP) BinaryNat.normalize_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem fromBitsLE_powerWord (k : ℕ) : Nat.fromBitsLE ((true :: List.replicate k false).reverse) = 2 ^ k := by
  rw [List.reverse_cons, List.reverse_replicate]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, Nat.fromBitsLE_cons, Bool.false_eq_true, ite_false, zero_add, ih, pow_succ]
    omega

theorem countCode_code (A W : List Bool → ℕ) (c : List Bool) : countCode A W c = BinaryNatCode.encode (count (A c) (W c)) := by
  rw [countCode, BinaryNat.normalize_eq_bits, fromBitsLE_powerWord]
  change (2 ^ (A c * W c)).bits = ((2 ^ W c) ^ A c).bits
  rw [← pow_mul, Nat.mul_comm (A c) (W c)]

@[simp] theorem countCode_length (A W : List Bool → ℕ) (c : List Bool) : (countCode A W c).length = A c * W c + 1 := by
  rw [countCode_code, BinaryNatCode.length_encode, count, ← pow_mul, Nat.size_pow]
  rw [Nat.mul_comm]

def rankTarget (q : List Bool) : List Bool := BinaryNat.normalize (pairSnd q)

theorem rankTarget_mem_FP : rankTarget ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP

def rankQuery (q : List Bool) : List Bool := pair (pair (pairFst q) (pairFst (pairSnd q))) (pairSnd (pairSnd q))

theorem rankQuery_mem_FP : rankQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def exponentRead (A W : List Bool → ℕ) (q : List Bool) : List Bool :=
  FixedWidthQuery.read (A ∘ pairFst) (W ∘ pairFst) rankTarget (rankQuery q)

theorem exponentRead_mem_FP {A W : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) : exponentRead A W ∈ FP :=
  mem_FP_comp rankQuery_mem_FP (FixedWidthQuery.read_mem_FP (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) rankTarget_mem_FP)

theorem exponentRead_packet (A W : List Bool → ℕ) (c : List Bool) (r i : ℕ) (hi : i < A c) :
    exponentRead A W (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i))) = BinaryNatCode.encode (entry (W c) r i) := by
  simp only [exponentRead, rankQuery, pairFst_pair, pairSnd_pair]
  rw [FixedWidthQuery.read_packet]
  simp only [FixedWidthQuery.entry, Function.comp_apply, pairFst_pair, hi, ite_true]
  unfold FixedWidthQuery.coordinate rankTarget
  simp only [pairSnd_pair, Function.comp_apply, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

end LeanCanny.Algebra.FixedWidthPolynomial

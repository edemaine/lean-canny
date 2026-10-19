/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryNatFP
public import Complexitylib.Classes.P.NatCodes

/-!
# FP lookup at a binary bit index

The query pairs a little-endian word with a binary index. Unary conversion is
capped at the word length; all larger indices return zero. The specification
covers arbitrary words and indices, including redundant high zeroes.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat
open Complexity

def bitAt (p : List Bool) : List Bool :=
  if (pairFst p)[Nat.fromBitsLE (pairSnd p)]?.getD false then [true] else []

theorem getD_min_length (word : List Bool) (k : ℕ) :
    word[min k word.length]?.getD false = word[k]?.getD false := by
  by_cases hk : k ≤ word.length
  · rw [min_eq_left hk]
  · have hl : word.length ≤ k := by omega
    simp only [min_eq_right hl, List.getElem?_eq_none (Nat.le_refl _),
      List.getElem?_eq_none hl]

theorem bitAt_mem_FP : bitAt ∈ FP := by
  have hk := UnaryFn.fromBitsLE_min pairSnd_mem_FP (UnaryFn.length pairFst_mem_FP)
  have h := (FPPred.getBit pairFst_mem_FP hk).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
  refine mem_FP_of_eq (g := bitAt) h ?_
  intro p
  simp only [bitAt, getD_min_length]

theorem fromBitsLE_testBit (word : List Bool) (k : ℕ) :
    (Nat.fromBitsLE word).testBit k = word[k]?.getD false := by
  induction word generalizing k with
  | nil => simp [Nat.fromBitsLE, Nat.fromBits]
  | cons b tail ih =>
    cases k with
    | zero =>
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.fromBitsLE_cons]
      cases b <;> simp [Nat.add_mod]
    | succ k =>
      have hhalf : Nat.fromBitsLE (b :: tail) / 2 = Nat.fromBitsLE tail := by
        rw [Nat.fromBitsLE_cons]
        cases b
        · simp
        · simp only [↓reduceIte]; omega
      rw [Nat.testBit_succ, hhalf, ih]
      rfl

theorem bitAt_pair (word index : List Bool) : bitAt (pair word index) =
    if (Nat.fromBitsLE word).testBit (Nat.fromBitsLE index) then [true] else [] := by
  simp only [bitAt, pairFst_pair, pairSnd_pair, fromBitsLE_testBit]

theorem bitAt_code (a k : ℕ) : bitAt (pair (BinaryNatCode.encode a) (BinaryNatCode.encode k)) =
    if a.testBit k then [true] else [] := by
  simp only [bitAt_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Encoding.BinaryNat

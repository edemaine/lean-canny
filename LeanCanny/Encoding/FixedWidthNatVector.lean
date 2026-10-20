/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryBitFP
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Bitwise

/-! # Fixed-width exponent vector words

An A-coordinate vector with W bits per coordinate takes exactly A*W bits.
Reading its i-th block recovers the original coordinate whenever it fits.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthNatVector
open Complexity

def encode (A W : ℕ) (e : ℕ → ℕ) : List Bool :=
  List.ofFn (fun k : Fin (A * W) => (e (k.val / W)).testBit (k.val % W))

@[simp] theorem length_encode (A W : ℕ) (e : ℕ → ℕ) : (encode A W e).length = A * W := List.length_ofFn

theorem block_encode (A W : ℕ) (e : ℕ → ℕ) (i : ℕ) (hi : i < A) :
    ((encode A W e).drop (i * W)).take W = List.ofFn (fun k : Fin W => (e i).testBit k.val) := by
  have hlen : i * W + W ≤ A * W := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right W hi
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, length_encode, List.length_ofFn]
    omega
  · intro k hk hk'
    have hkW : k < W := by simpa only [List.length_ofFn] using hk'
    have hW : 0 < W := by omega
    have hdiv : (i * W + k) / W = i := by
      rw [Nat.mul_comm i W, Nat.add_comm, Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt hkW, Nat.zero_add]
    have hmod : (i * W + k) % W = k := by
      rw [Nat.mul_comm i W, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hkW]
    simp only [List.getElem_take, List.getElem_drop, encode, List.getElem_ofFn, hdiv, hmod]

theorem fromBitsLE_ofFn_testBit (W n : ℕ) (hn : n < 2 ^ W) :
    Nat.fromBitsLE (List.ofFn (fun k : Fin W => n.testBit k.val)) = n := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [BinaryNat.fromBitsLE_testBit]
  by_cases hk : k < W
  · simp [hk]
  · have hW : W ≤ k := by omega
    have hlarge := Nat.testBit_eq_false_of_lt (hn.trans_le (Nat.pow_le_pow_right (by decide) hW))
    simp [hk, hlarge]

theorem decode_block (A W : ℕ) (e : ℕ → ℕ) (i : ℕ) (hi : i < A) (he : e i < 2 ^ W) :
    Nat.fromBitsLE (((encode A W e).drop (i * W)).take W) = e i := by
  rw [block_encode A W e i hi]
  exact fromBitsLE_ofFn_testBit W (e i) he

end LeanCanny.Encoding.FixedWidthNatVector

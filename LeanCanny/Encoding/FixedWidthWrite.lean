/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native FP replacement of one fixed-width table cell

The output always has the prescribed length. A fitting replacement is read
back exactly; every other in-range cell retains its decoded value. Indices
and replacement values stay binary, including on malformed input tables.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthQuery
open LeanCanny.Encoding.Brackets

def write (A W : List Bool → ℕ) (target : List Bool → List Bool) (index value : List Bool → ℕ) (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (A c) (W c) (fun k => if k = index c then value c else entry A W target c k)

theorem coordinate_lt (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    coordinate W target c k < 2 ^ W c :=
  (Nat.fromBitsLE_lt_pow_length _).trans_le (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem entry_lt (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (k : ℕ) :
    entry A W target c k < 2 ^ W c := by
  unfold entry
  split_ifs
  · exact coordinate_lt W target c k
  · exact Nat.two_pow_pos _

theorem write_mem_FP {A W : List Bool → ℕ} {target : List Bool → List Bool} {index value : List Bool → ℕ}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) (hi : BinaryFn index) (hv : BinaryFn value) :
    write A W target index value ∈ FP := by
  have hindex := mem_FP_comp pairFst_mem_FP hi.bits_mem_FP
  have hp : FPPred (fun p => Nat.fromBitsLE (pairSnd p) = index (pairFst p)) :=
    by simpa only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      BinaryNat.eq_fppred pairSnd_mem_FP hindex
  let readCell := fun p => if Nat.fromBitsLE (pairSnd p) = index (pairFst p) then
    BinaryNatCode.encode (value (pairFst p)) else read A W target p
  have hread : readCell ∈ FP := hp.ite_mem_FP (mem_FP_comp pairFst_mem_FP hv.bits_mem_FP) (read_mem_FP hA hW ht)
  apply FixedWidthNatVector.encode_mem_FP A W (fun c k => if k = index c then value c else entry A W target c k)
    hA hW readCell hread
  intro c k
  simp only [readCell, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs
  · rfl
  · exact read_packet A W target c k

theorem write_length (A W : List Bool → ℕ) (target : List Bool → List Bool) (index value : List Bool → ℕ) (c : List Bool) :
    (write A W target index value c).length = A c * W c := FixedWidthNatVector.length_encode _ _ _

theorem entry_write (A W : List Bool → ℕ) (target : List Bool → List Bool) (index value : List Bool → ℕ)
    (c : List Bool) (k : ℕ) (hk : k < A c) (hv : value c < 2 ^ W c) :
    entry A W (write A W target index value) c k = if k = index c then value c else entry A W target c k := by
  rw [entry, ite_eq_left hk, coordinate, write]
  apply FixedWidthNatVector.decode_block _ _ _ k hk
  split_ifs
  · exact hv
  · exact entry_lt A W target c k

end LeanCanny.Encoding.FixedWidthQuery

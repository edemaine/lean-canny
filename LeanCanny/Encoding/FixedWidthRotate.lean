/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Native rotation of fixed-width coordinate records

The first old coordinate is the last new coordinate; each other old coordinate
moves down by one. Binary indices remain binary in the total packet reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.FixedWidthRotate
open Brackets Turing.MultiTapeTM

def index (A : ℕ) (i : ℕ) : ℕ := if i = 0 then A - 1 else i - 1

def read (A W : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) : List Bool :=
  FixedWidthQuery.read A W target (pair (pairFst q)
    (if Nat.fromBitsLE (pairSnd q) = 0 then BinaryNatCode.encode (A (pairFst q) - 1)
      else BinaryNat.sub (pair (pairSnd q) (BinaryNatCode.encode 1))))

theorem read_mem_FP {A W : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) : read A W target ∈ FP := by
  have hp := (BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const 0)
  have hz := (BinaryFn.ofUnary (hA.comp pairFst_mem_FP)).sub (BinaryFn.const 1)
  have hi := hp.ite_mem_FP hz.bits_mem_FP
    (mem_FP_comp (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP)
  exact mem_FP_comp (mem_FP_pair pairFst_mem_FP hi) (FixedWidthQuery.read_mem_FP hA hW ht)

theorem read_packet (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    read A W target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.entry A W target c (index (A c) i)) := by
  simp only [read, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs with hi
  · simpa only [index, hi, ite_true, BinaryNatCode.encode] using FixedWidthQuery.read_packet A W target c (A c - 1)
  · rw [BinaryNat.sub_pair]
    simpa only [Nat.fromBitsLE_bits, index, hi, ite_false, BinaryNatCode.encode] using
      FixedWidthQuery.read_packet A W target c (i - 1)

def word (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (A c) (W c) (fun i => FixedWidthQuery.entry A W target c (index (A c) i))

theorem word_mem_FP {A W : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) : word A W target ∈ FP :=
  FixedWidthNatVector.encode_mem_FP A W _ (hA) hW (read A W target) (read_mem_FP hA hW ht) (read_packet A W target)

theorem coordinate (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool)
    (i : ℕ) (hi : i < A c) :
    FixedWidthQuery.coordinate W (word A W target) c i = FixedWidthQuery.entry A W target c (index (A c) i) := by
  apply FixedWidthNatVector.decode_block (A c) (W c) _ i hi
  unfold FixedWidthQuery.entry FixedWidthQuery.coordinate
  split_ifs
  · exact (Nat.fromBitsLE_lt_pow_length _).trans_le
      (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))
  · exact Nat.two_pow_pos _

end LeanCanny.Encoding.FixedWidthRotate

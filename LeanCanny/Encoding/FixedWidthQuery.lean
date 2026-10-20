/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthNatVectorFP
public import LeanCanny.Encoding.BinarySubFP
public import Complexitylib.Classes.P.BoundedQuant

/-! # Uniform FP access and repacking for exponent queries

An arbitrary target word supplies fixed-width blocks. A bounded prefix reader
returns zero outside its dimension, while capping binary indices keeps block
access polynomial-time. Repacking changes widths and pads coordinates without
materializing numbers in unary. Bounded coordinate guards are in FP.
-/

@[expose] public section

namespace LeanCanny.Encoding.FixedWidthQuery
open Complexity

def coordinate (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℕ :=
  Nat.fromBitsLE (((target c).drop (i * W c)).take (W c))

def entry (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) : ℕ :=
  if i < A c then coordinate W target c i else 0

def read (A W : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) < A (pairFst q) then
    BinaryNat.normalize (((target (pairFst q)).drop
      (min (Nat.fromBitsLE (pairSnd q)) (A (pairFst q)) * W (pairFst q))).take (W (pairFst q))) else []

theorem read_mem_FP {A W : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (ht : target ∈ FP) : read A W target ∈ FP := by
  have hi := UnaryFn.fromBitsLE_min pairSnd_mem_FP hA.lift
  have hw := hW.lift
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (hi.mul hw)) hw
  have hp : FPPred (fun q => Nat.fromBitsLE (pairSnd q) < A (pairFst q)) := by
    apply (BinaryNat.lt_fppred pairSnd_mem_FP (bits_mem_FP hA.lift)).of_iff
    intro q
    simp only [Nat.fromBitsLE_bits]
  have h := hp.ite_mem_FP (mem_FP_comp hs BinaryNat.normalize_mem_FP) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

theorem read_packet (A W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    read A W target (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (entry A W target c i) := by
  simp only [read, pairFst_pair, pairSnd_pair,
    show Nat.fromBitsLE (BinaryNatCode.encode i) = i from Nat.fromBitsLE_bits i]
  by_cases hi : i < A c
  · simp only [hi, ite_true, min_eq_left hi.le, entry, BinaryNat.normalize_eq_bits, coordinate, BinaryNatCode.encode]
  · simp only [hi, ite_false, entry, BinaryNatCode.encode]
    rfl

def repack (A W B V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (B c) (V c) (entry A W target c)

theorem repack_mem_FP {A W B V : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hB : UnaryFn B) (hV : UnaryFn V) (ht : target ∈ FP) :
    repack A W B V target ∈ FP :=
  FixedWidthNatVector.encode_mem_FP B V (entry A W target) hB hV (read A W target)
    (read_mem_FP hA hW ht) (read_packet A W target)

@[simp] theorem repack_length (A W B V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) :
    (repack A W B V target c).length = B c * V c := FixedWidthNatVector.length_encode _ _ _

theorem coordinate_repack (A W B V : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool)
    (i : ℕ) (hi : i < B c) (he : entry A W target c i < 2 ^ V c) :
    coordinate V (repack A W B V target) c i = entry A W target c i :=
  FixedWidthNatVector.decode_block (B c) (V c) (entry A W target c) i hi he

def Bounded (A W : List Bool → ℕ) (target : List Bool → List Bool) (bound : List Bool → ℕ) (c : List Bool) : Prop :=
  ∀ i < A c, coordinate W target c i ≤ bound c

theorem bounded_fppred {A W bound : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hb : UnaryFn bound) (ht : target ∈ FP) : FPPred (Bounded A W target bound) := by
  have hw := hW.lift
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hw)) hw
  have hp := BinaryNat.le_fppred hs (bits_mem_FP hb.lift)
  apply (FPPred.forall_lt hA hp).of_iff
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    Nat.fromBitsLE_bits, Bounded, coordinate]

theorem entry_le_of_bounded (A W bound : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool)
    (h : Bounded A W target bound c) (i : ℕ) : entry A W target c i ≤ bound c := by
  unfold entry
  split_ifs with hi
  · exact h i hi
  · exact Nat.zero_le _

end LeanCanny.Encoding.FixedWidthQuery

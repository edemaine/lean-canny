/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionGuard
public import LeanCanny.ETR.TubeZeroQuery

/-! # FP projection-to-tube exponent queries

Drop the direction block, preserve point and parameter exponents, and optionally
increment one tube coordinate for a derivative query. A width of W+1 preserves
the increment even at the largest W-bit exponent. Binary indices are capped
before conversion to unary, so malformed query indices remain polynomial-time.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery

open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding

attribute [local irreducible] BinaryNat.succ FixedWidthQuery.read

def entry (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool) (c : List Bool) (i : ℕ) : ℕ :=
  if i < TubeEncoding.dimension (n c) then
    FixedWidthQuery.coordinate W target c (embeddedIndex (n c) i) +
      (if bumped then (if i = r c then 1 else 0) else 0)
  else 0

def capped (n : List Bool → ℕ) (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (pairSnd q)) (TubeEncoding.dimension (n (pairFst q)))

def block (n W : List Bool → ℕ) (target : List Bool → List Bool) (q : List Bool) : List Bool :=
  FixedWidthQuery.read (fun c => TubeProjectionEncoding.dimension (n c)) W target
    (pair (pairFst q) (BinaryNatCode.encode (embeddedIndex (n (pairFst q)) (capped n q))))

def read (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd q) < TubeEncoding.dimension (n (pairFst q)) then
    if bumped then (if capped n q = r (pairFst q) then BinaryNat.succ (block n W target q) else block n W target q)
    else block n W target q
  else []

theorem capped_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (capped n) :=
  UnaryFn.fromBitsLE_min pairSnd_mem_FP (TubeZeroQuery.dimension_unary hn).lift

theorem embeddedIndex_unary {n i : List Bool → ℕ} (hn : UnaryFn n) (hi : UnaryFn i) :
    UnaryFn (fun c => embeddedIndex (n c) (i c)) :=
  UnaryFn.ite (FPPred.lt hi (pointCount_unary hn)) hi (hi.add (pointCount_unary hn))

theorem block_mem_FP {n W : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (ht : target ∈ FP) : block n W target ∈ FP := by
  have hi := embeddedIndex_unary hn.lift (capped_unary hn)
  have hq := mem_FP_pair pairFst_mem_FP (bits_mem_FP hi)
  have h := mem_FP_comp hq (FixedWidthQuery.read_mem_FP (dimension_unary hn) hW ht)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem read_mem_FP {n W r : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) (bumped : Bool) : read n W r target bumped ∈ FP := by
  have hb := block_mem_FP hn hW ht
  have he := FPPred.eq (capped_unary hn) hr.lift
  have hs := he.ite_mem_FP (mem_FP_comp hb BinaryNat.succ_mem_FP) hb
  have hp : FPPred (fun q => Nat.fromBitsLE (pairSnd q) < TubeEncoding.dimension (n (pairFst q))) := by
    apply (BinaryNat.lt_fppred pairSnd_mem_FP (bits_mem_FP (TubeZeroQuery.dimension_unary hn).lift)).of_iff
    intro q
    simp only [Nat.fromBitsLE_bits]
  cases bumped
  · exact hp.ite_mem_FP hb (constFn_mem_FP [])
  · exact hp.ite_mem_FP hs (constFn_mem_FP [])

theorem block_packet (n W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ)
    (hi : i < TubeEncoding.dimension (n c)) :
    block n W target (pair c (BinaryNatCode.encode i)) =
      BinaryNatCode.encode (FixedWidthQuery.coordinate W target c (embeddedIndex (n c) i)) := by
  have hcode (j : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode j) = j := Nat.fromBitsLE_bits j
  unfold block capped
  simp only [pairFst_pair, pairSnd_pair, hcode, min_eq_left hi.le]
  rw [FixedWidthQuery.read_packet]
  unfold FixedWidthQuery.entry
  rw [ite_eq_left (embeddedIndex_lt (n c) i hi)]

theorem read_packet (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool) (c : List Bool) (i : ℕ) :
    read n W r target bumped (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (entry n W r target bumped c i) := by
  have hcode (j : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode j) = j := Nat.fromBitsLE_bits j
  unfold read entry
  simp only [pairFst_pair, pairSnd_pair, hcode]
  by_cases hi : i < TubeEncoding.dimension (n c)
  · rw [ite_eq_left hi, ite_eq_left hi, block_packet n W target c i hi]
    have hc : capped n (pair c (BinaryNatCode.encode i)) = i := by
      simp only [capped, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, min_eq_left hi.le]
    rw [hc]
    cases bumped <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero]
    split_ifs <;> simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, add_zero]
  · rw [ite_eq_right hi, ite_eq_right hi]
    rfl

def repacked (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool) (c : List Bool) : List Bool :=
  FixedWidthNatVector.encode (TubeEncoding.dimension (n c)) (W c + 1) (entry n W r target bumped c)

theorem repacked_mem_FP {n W r : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) (bumped : Bool) : repacked n W r target bumped ∈ FP :=
  FixedWidthNatVector.encode_mem_FP _ _ _ (TubeZeroQuery.dimension_unary hn) (hW.add (UnaryFn.const 1))
    (read n W r target bumped) (read_mem_FP hn hW hr ht bumped) (read_packet n W r target bumped)

theorem coordinate_lt (W : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) (i : ℕ) :
    FixedWidthQuery.coordinate W target c i < 2 ^ W c := by
  exact (Nat.fromBitsLE_lt_pow_length _).trans_le
    (Nat.pow_le_pow_right (by decide) (List.length_take_le _ _))

theorem entry_lt (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool) (c : List Bool) (i : ℕ) :
    entry n W r target bumped c i < 2 ^ (W c + 1) := by
  have h := coordinate_lt W target c (embeddedIndex (n c) i)
  have hp := Nat.two_pow_pos (W c)
  unfold entry
  rw [pow_succ]
  split_ifs <;> omega

theorem coordinate_repacked (n W r : List Bool → ℕ) (target : List Bool → List Bool) (bumped : Bool)
    (c : List Bool) (i : ℕ) (hi : i < TubeEncoding.dimension (n c)) :
    FixedWidthQuery.coordinate (fun c => W c + 1) (repacked n W r target bumped) c i = entry n W r target bumped c i :=
  FixedWidthNatVector.decode_block _ _ _ i hi (entry_lt n W r target bumped c i)

end LeanCanny.ETR.TubeProjectionQuery

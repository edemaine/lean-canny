/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FixedWidthQuery
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Binary degree guards for fixed-width exponent queries

The number of variables and exponent-block widths remain polynomially bounded
in unary. The exponent allowance itself can be exponentially large and is
compared in binary without a unary conversion.
-/

@[expose] public section
namespace LeanCanny.Encoding.FixedWidthQuery

theorem bounded_binary_fppred {A W bound : List Bool → ℕ} {target : List Bool → List Bool}
    (hA : UnaryFn A) (hW : UnaryFn W) (hb : BinaryFn bound) (ht : target ∈ FP) :
    FPPred (Bounded A W target bound) := by
  have hw := hW.lift
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hw)) hw
  have hbound : BinaryFn (fun q => bound (pairFst q)) := hb.comp pairFst_mem_FP
  have hp := BinaryNat.le_fppred hs hbound.bits_mem_FP
  apply (FPPred.forall_lt hA hp).of_iff
  intro c
  simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Bounded, coordinate]

end LeanCanny.Encoding.FixedWidthQuery

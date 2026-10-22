/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionPattern
public import LeanCanny.ETR.TubeZeroFP

/-! # FP direction-pattern checks for projection coefficient access -/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery

open LeanCanny.Encoding
open TubeProjectionEncoding

theorem pointCount_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun c => pointCount (n c)) :=
  hn.add (TubeZero.constraintCount_unary hn)

theorem dimension_unary {n : List Bool → ℕ} (hn : UnaryFn n) : UnaryFn (fun c => dimension (n c)) :=
  ((pointCount_unary hn).add (pointCount_unary hn)).add (UnaryFn.const 3)

theorem expected_mem_FP {r : List Bool → ℕ} (hr : UnaryFn r) (shifted : Bool) :
    (fun q => BinaryNatCode.encode (expected (if shifted then some (r (pairFst q)) else none) (pairSnd q).length)) ∈ FP := by
  cases shifted with
  | false => exact constFn_mem_FP []
  | true =>
    have h := (FPPred.eq hr.lift UnaryFn.index).ite_mem_FP (constFn_mem_FP [true]) (constFn_mem_FP [])
    apply mem_FP_of_eq h
    intro q
    simp only [ite_true, expected, Option.some.injEq]
    split_ifs <;> rfl

theorem pattern_fppred {n W r : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) (shifted : Bool) :
    FPPred (Pattern n W target (fun c => if shifted then some (r c) else none)) := by
  have hw := hW.lift
  have hi := (pointCount_unary hn).lift.add UnaryFn.index
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (hi.mul hw)) hw
  have he := expected_mem_FP hr shifted
  have hp : FPPred (fun q => FixedWidthQuery.coordinate W target (pairFst q)
      (pointCount (n (pairFst q)) + (pairSnd q).length) =
        expected (if shifted then some (r (pairFst q)) else none) (pairSnd q).length) := by
    apply ((BinaryNat.le_fppred hs he).and (BinaryNat.le_fppred he hs)).of_iff
    intro q
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  apply (FPPred.forall_lt (pointCount_unary hn) hp).of_iff
  intro c
  simp only [Pattern, pairFst_pair, pairSnd_pair, List.length_replicate]

end LeanCanny.ETR.TubeProjectionQuery

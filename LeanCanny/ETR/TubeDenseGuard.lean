/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDenseEncoding

/-! # FP checks for dense tube shift patterns

The point block is unrestricted here. Every other coordinate is compared in
binary with the zero or unit exponent dictated by the selected shift term.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDense

open LeanCanny.Encoding

theorem expected_mem_FP {n : List Bool → ℕ} (hn : UnaryFn n) (s : Option Bool) :
    (fun q => BinaryNatCode.encode (expected (n (pairFst q)) s (pairSnd q).length)) ∈ FP := by
  cases s with
  | none => exact constFn_mem_FP []
  | some b =>
    have h := (FPPred.eq UnaryFn.index (hn.lift.add (UnaryFn.const (if b then 1 else 0)))).ite_mem_FP
      (constFn_mem_FP [true]) (constFn_mem_FP [])
    apply mem_FP_of_eq h
    intro q
    simp only [expected]
    split_ifs <;> rfl

theorem pattern_fppred {n W : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (ht : target ∈ FP) (s : Option Bool) : FPPred (Pattern n W target s) := by
  have hw := hW.lift
  have hs := take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.mul hw)) hw
  have he := expected_mem_FP hn s
  have hp : FPPred (fun q => FixedWidthQuery.coordinate W target (pairFst q) (pairSnd q).length =
      expected (n (pairFst q)) s (pairSnd q).length) := by
    simpa only [FixedWidthQuery.coordinate, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      BinaryNat.eq_fppred hs he
  have hor := (FPPred.lt UnaryFn.index hn.lift).or hp
  apply (FPPred.forall_lt (TubeZeroQuery.dimension_unary hn) hor).of_iff
  intro c
  simp only [Pattern, pairFst_pair, pairSnd_pair, List.length_replicate]
  constructor
  · intro h i hi hn
    exact (h i hi).resolve_left (by omega)
  · intro h i hi
    by_cases hn : i < n c
    · exact Or.inl hn
    · exact Or.inr (h i hi (by omega))

end LeanCanny.ETR.TubeDense

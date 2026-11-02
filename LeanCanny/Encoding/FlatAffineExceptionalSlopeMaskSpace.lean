/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalInverseSelectorSpace
public import LeanCanny.Computation.SpaceFunctionSelect
/-! # Actual slope masks use original flags and original integer-leading products -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem initial_denominator_space {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP) :
    SpaceFunction (fun q => residueBits (FlatAffineExceptionalBankSource.denominator F C h (input q) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  have H := (FlatAffineExceptionalBankSource.denominator_evaluator hF C h (height_unary hF h hh)).precompose
    (fun q => pair (input q) (mod q)) (mem_FP_pair hi hm)
  apply H.congr
  funext q
  exact congrArg₂ (fun (u m : List Bool) => residueBits (FlatAffineExceptionalBankSource.denominator F C h u : ZMod (Nat.fromBitsLE m + 1)))
    (pairFst_pair _ _) (pairSnd_pair _ _)

theorem initial_slope_mask_space {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP) (A : List Bool → ℕ) (hA : BinaryFn A) :
    SpaceFunction (fun q => residueBits ((if A q = ((FlatAffineExceptionalOrderedRule.order F (input q)).symm (h (input q))).val then
      FlatAffineExceptionalBankSource.denominator F C h (input q) else 0) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  let K := fun q => ((FlatAffineExceptionalOrderedRule.order F (input q)).symm (h (input q))).val
  have HA : BinaryFn (fun p => A (pairFst p)) := hA.comp pairFst_mem_FP
  have HP := HA.eq (BinaryFn.fromBits pairSnd_mem_FP)
  have HF0 := (inverse_evaluator hF input hi h hh).withInput.postcompose _ HP.flag_mem_FP
  have HF : SpaceFunction (fun q => [decide (A q = K q)]) := by
    apply HF0.congr
    funext q
    exact congrArg₂ (fun (i j : ℕ) => [decide (i = j)]) (congrArg A (pairFst_pair _ _))
      (by simp only [pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
  have H := SpaceFunction.select HF (initial_denominator_space hF C h hh input mod hi hm)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  apply H.congr
  funext q
  simp only [List.getElem?_cons_zero, Option.getD_some, decide_eq_true_eq]
  split_ifs
  · rfl
  · simpa only [ArithmeticBits.zero, Int.cast_zero] using ArithmeticBits.zero_residueBits (Nat.fromBitsLE (mod q) + 1)

theorem actual_slope_mask_space {F : Inputs} (hF : F.Access) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : BinaryFn (fun u => (h u).val))
    (input mod : List Bool → List Bool) (hi : input ∈ FP) (hm : mod ∈ FP) (A : List Bool → ℕ) (hA : BinaryFn A)
    (S : List Bool → ℕ) (hb : ∀ q, FlatAffineExceptionalBankSource.births F (input q) ≤ S q)
    (hf : ∀ q, h (input q) ∈ FlatAffineExceptionalOrderedRule.frozen F (input q))
    (r : (q : List Bool) → Fin (arity F (input q))) (hr : ∀ q, r q ∉ FlatAffineExceptionalOrderedRule.frozen F (input q)) :
    SpaceFunction (fun q => residueBits ((if A q = (FlatAffineExceptionalOrderedRule.sweep F C h (S q) (input q) (hb q) (hf q) (r q) (hr q)).height.val then
      (FlatAffineExceptionalOrderedRule.sweep F C h (S q) (input q) (hb q) (hf q) (r q) (hr q)).slope else 0) : ZMod (Nat.fromBitsLE (mod q) + 1))) := by
  apply (initial_slope_mask_space hF C h hh input mod hi hm A hA).congr
  funext q
  rw [FlatAffineExceptionalSlopeSource.slope_eq]
  rfl
end LeanCanny.Encoding.FlatAffineExceptionalSelectorSpace

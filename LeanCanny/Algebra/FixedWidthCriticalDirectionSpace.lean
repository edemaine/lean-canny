/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthCriticalSpace

/-! # Critical coefficients with a space-computed direction

Derivative outputs and the direction entry are cached before modular
arithmetic. The direction search is included in the native space bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCriticalBits
open LeanCanny.Encoding LeanCanny.Computation

variable (A W D base selected : List Bool → ℕ) (target modulus direction : List Bool → List Bool)

/-- Cache a space-computed direction alongside the derivative coefficients. -/
private def cacheDirection (z : List Bool) : List Bool :=
  pair (pair (pairFst z) (pairSnd (pairSnd z))) (pairFst (pairSnd z))

private theorem cacheDirection_mem_FP : cacheDirection ∈ FP := by
  polytime [cacheDirection]

theorem difference_evaluator_space {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hb : UnaryFn base) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (V : SpaceFunction direction) :
    SpaceFunction (difference A W D base selected target modulus direction coefficient) := by
  have EL := FixedWidthDerivativeBits.evaluator_binary_degree A W W D selected target modulus E hA hW hW hD hs ht hm
  have ER := FixedWidthDerivativeBits.evaluator_binary_degree A W W D base target modulus E hA hW hW hD hb ht hm
  have H := (((EL.pairOutputs ER).pairOutputs V).withInput.postcompose cacheDirection cacheDirection_mem_FP).postcompose
    (finish (modulus ∘ pairFst) pairSnd)
    (finish_mem_FP (modulus ∘ pairFst) pairSnd (mem_FP_comp pairFst_mem_FP hm) pairSnd_mem_FP)
  apply H.congr
  funext c
  simp only [Function.comp_apply, cacheDirection, finish, scaled, pairFst_pair, pairSnd_pair, difference]

/-- Direction selection may itself require polynomial space. -/
theorem evaluator_space {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) (hb : UnaryFn base) (hs : UnaryFn selected)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (V : SpaceFunction direction) :
    SpaceFunction (value A W D base selected target modulus direction coefficient) := by
  have EL := E.precompose (sourceQuery target) (sourceQuery_mem_FP target ht)
  have ER := difference_evaluator_space A W D base selected target modulus direction E hA hW hD hb hs ht hm V
  have H := SpaceFunction.branch (fun c => decide (selected c = base c)) (FPPred.eq hs hb).flag_mem_FP EL ER
  exact H.congr (funext fun c => by simp only [value, Function.comp_apply, decide_eq_true_eq])

end LeanCanny.Algebra.FixedWidthCriticalBits

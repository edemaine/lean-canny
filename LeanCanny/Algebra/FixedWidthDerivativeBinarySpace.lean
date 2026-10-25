/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthDerivativeSpace
public import LeanCanny.Encoding.FixedWidthQueryBinary

/-! # Native derivative coefficients with binary degree bounds

The existing coefficient program and its exact coefficient specification are
unchanged. Its guard has a binary-degree certificate, allowing exponential
degree values while retaining polynomially bounded exponent-block widths.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical

theorem evaluator_binary_degree (A W V D selected : List Bool → ℕ)
    (target modulus : List Bool → List Bool)
    {coefficient : List Bool → List Bool} (E : SpaceFunction coefficient)
    (hA : UnaryFn A) (hW : UnaryFn W) (hV : UnaryFn V) (hD : BinaryFn D)
    (hs : UnaryFn selected) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value A W V D selected target modulus coefficient) := by
  have EQ := ((E.precompose (query A W V selected target)
    (query_mem_FP A W V selected target hA hW hV hs ht)).withInput).postcompose
      (finish A V selected target modulus) (finish_mem_FP A V selected target modulus hA hV hs ht hm)
  have hb := FixedWidthQuery.bounded_binary_fppred hA hV (hD.sub (BinaryFn.const 1)) ht
  have EB := SpaceFunction.branch (fun c => decide (FixedWidthQuery.Bounded A V target (fun c => D c - 1) c))
    hb.flag_mem_FP EQ (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  exact EB.congr (funext fun c => by simp only [value, Function.comp_apply, decide_eq_true_eq])

end LeanCanny.Algebra.FixedWidthDerivativeBits

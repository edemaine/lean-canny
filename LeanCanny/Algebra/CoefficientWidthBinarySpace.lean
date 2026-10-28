/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientWidthSpace
public import LeanCanny.Encoding.FixedWidthQueryBinary

/-! # Native exponent-width changes with binary degree allowances

The existing guarded program and its coefficient packet are unchanged.
Only the degree allowance is binary; variable counts and exponent widths
retain unary polynomial bounds. Oversized exponents are rejected before
repacking, so narrowing cannot turn them into supported monomials.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoefficientWidthBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial

theorem fits_binary_fppred {A W D : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W) (hD : BinaryFn D) :
    FPPred (Fits A W D) :=
  FixedWidthQuery.bounded_binary_fppred (hA.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (hD.comp pairFst_mem_FP) rankTarget_mem_FP

theorem evaluator_binary_degree {A W V D : List Bool → ℕ} (hA : UnaryFn A) (hW : UnaryFn W)
    (hV : UnaryFn V) (hD : BinaryFn D) {reader : List Bool → List Bool} (E : SpaceFunction reader) :
    SpaceFunction (value A W V D reader) := by
  have EC := E.precompose (sourceQuery A W V) (sourceQuery_mem_FP hA hW hV)
  exact (SpaceFunction.branch (fun q => decide (Fits A W D q)) (fits_binary_fppred hA hW hD).flag_mem_FP
    EC (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

end LeanCanny.Algebra.CoefficientWidthBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalSpace
public import LeanCanny.Algebra.PreparedPolynomialContext

/-! # Space-computed clearing exponents in native univariate composition

Storing the exponent in a prepared context supplies the native routine's FP
controls. Every stored exponent defines a valid truncated clearing operation,
so this substitution requires no polynomial-degree validation or time bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRationalBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation

theorem evaluatorWithExponent (p n d : List Bool → ℤ[X]) (e : List Bool → ℕ)
    (E : SpaceFunction (fun c => BinaryNatCode.encode (e c)))
    (P : SpaceFunction (PrimitivePairBits.coefficient p)) (N : SpaceFunction (PrimitivePairBits.coefficient n))
    (D : SpaceFunction (PrimitivePairBits.coefficient d)) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => UnivariateRational.clear (e c) (p c) (n c) (d c))) := by
  have hp := PrimitivePairBits.withContextEvaluator p pairFst (SpaceFunction.ofFP pairFst pairFst_mem_FP) P
  have hn := PrimitivePairBits.withContextEvaluator n pairFst (SpaceFunction.ofFP pairFst pairFst_mem_FP) N
  have hd := PrimitivePairBits.withContextEvaluator d pairFst (SpaceFunction.ofFP pairFst pairFst_mem_FP) D
  have he : BinaryFn (fun c => Nat.fromBitsLE (pairSnd c)) := BinaryFn.fromBits pairSnd_mem_FP
  have Q := evaluator (p ∘ pairFst) (n ∘ pairFst) (d ∘ pairFst) _ he hp hn hd
  have R := PrimitivePairBits.withContextEvaluator _ (fun c => LeanCanny.pair c (BinaryNatCode.encode (e c))) E.withInput Q
  refine R.congr (funext fun q => ?_)
  simp only [PrimitivePairBits.coefficient, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Algebra.UnivariateRationalBits

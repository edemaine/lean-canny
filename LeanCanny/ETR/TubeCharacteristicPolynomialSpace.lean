/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicPolynomial
public import LeanCanny.ETR.TubeCharacteristicQuotientSpace

/-! # Polynomial-space access to the tube polynomial's lowest degree

The existing signed-order evaluator now returns the actual polynomial
trailing degree. Its nonnegative component gives a natural index evaluator,
and a positive index decides whether the polynomial's constant coefficient
vanishes. All original source-reader and suspended-child costs are retained.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree

noncomputable def polynomialLowestIndexCode (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (polynomial source active n d ell c).natTrailingDegree

noncomputable def polynomialLowestIndexEvaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (polynomialLowestIndexCode source active n d ell) := by
  have E := (orderEvaluator D).postcompose pairFst pairFst_mem_FP
  refine E.congr (funext fun c => ?_)
  simp only [Function.comp_apply, orderCode, SignStatisticBits.integerCode, pairFst_pair, order_eq_polynomial,
    Int.toNat_natCast, polynomialLowestIndexCode]

theorem polynomialConstantZero_mem_PSPACE {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    {c | (polynomial source active n d ell c).coeff 0 = 0} ∈ PSPACE := by
  have hf := (BinaryNat.lt_fppred (constFn_mem_FP []) id_mem_FP).flag_mem_FP
  apply SpaceDecider.mem_PSPACE
  refine (polynomialLowestIndexEvaluator D).decider (fun w => decide (0 < Nat.fromBitsLE w)) hf ?_
  intro c
  simp only [polynomialLowestIndexCode, MacaulayBits.fromBits_encode, decide_eq_true_eq, Set.mem_ofPred_eq,
    Nat.pos_iff_ne_zero, Polynomial.natTrailingDegree_ne_zero]
  constructor
  · intro h
    exact ⟨polynomial_ne_zero source active n d ell c, h⟩
  · exact And.right

end LeanCanny.ETR.TubeCharacteristicQuotient

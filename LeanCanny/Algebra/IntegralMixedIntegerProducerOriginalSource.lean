/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSpace
/-! # Original integer-source access supplies charged degree and coefficient leaves

A literal polynomial-source transport, with native degree/mass upper bounds
and a charged original coefficient reader, constructs both required leaves.
The exact degree is computed in space rather than supplied in polynomial time.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

def coefficientPullback (query : List Bool → List Bool) (z : List Bool) : List Bool :=
  pair (pair (query (pairFst (pairFst z))) (pairSnd (pairFst z))) (pairSnd z)
theorem coefficientPullback_FP (query : List Bool → List Bool) (hq : query ∈ FP) : coefficientPullback query ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hq)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem original_of_source (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (query : List Bool → List Bool) (hq : query ∈ FP)
    (hp : ∀ q, polynomial P D q = S.polynomial (query q)) : Original P D where
  degree := by
    have E := IntegerPolynomialBits.degreeEvaluator S.polynomial hS.coefficient S.degree S.mass hS.degree hS.mass
      S.degree_bound S.mass_bound
    refine (E.precompose query hq).congr (funext fun q => ?_)
    change BinaryNatCode.encode (S.polynomial (query q)).natDegree = BinaryNatCode.encode (polynomial P D q).natDegree
    rw [hp]
  coefficient := by
    refine (hS.coefficient.precompose (coefficientPullback query) (coefficientPullback_FP query hq)).congr (funext fun z => ?_)
    simp only [Function.comp_apply, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
      coefficientPullback, pairFst_pair, pairSnd_pair]
    rw [hp]

end LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceBits

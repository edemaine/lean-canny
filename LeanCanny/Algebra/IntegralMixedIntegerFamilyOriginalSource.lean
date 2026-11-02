/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerFamilySpace
public import LeanCanny.Algebra.IntegralMixedIntegerProducerOriginalSource
/-! # Original integer-source queries feed arbitrary retained-prefix producers

The query uses the entire saved key. The original source supplies established
coefficient access and native upper bounds; exact degree is computed in space.
No interpretation of the retained algebra is used by this adapter.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedIntegerFamilyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

theorem original_of_source (P : Parameters) (a : Access P) (p : List Bool → Polynomial ℤ)
    (S : IntegerPolynomialRootQueriesBits.Source) (hS : IntegerPolynomialRootQueriesBits.Access S)
    (query : List Bool → List Bool) (hq : query∈FP)
    (hp : ∀ key, p key=S.polynomial (query key)) : Original P p where
  degree := by
    have E := IntegerPolynomialBits.degreeEvaluator S.polynomial hS.coefficient S.degree S.mass hS.degree hS.mass
      S.degree_bound S.mass_bound
    have HQ := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) hq
    refine (E.precompose (query ∘ IntegralMixedVirtualTaskBits.saved P) HQ).congr (funext fun q => ?_)
    change BinaryNatCode.encode (S.polynomial (query (IntegralMixedVirtualTaskBits.saved P q))).natDegree=
      BinaryNatCode.encode (p (IntegralMixedVirtualTaskBits.saved P q)).natDegree
    rw [hp]
  coefficient := by
    have HQ := mem_FP_comp (IntegralMixedVirtualTaskBits.saved_FP P a) hq
    refine (hS.coefficient.precompose
      (IntegralMixedIntegerProducerSpaceBits.coefficientPullback (query ∘ IntegralMixedVirtualTaskBits.saved P))
      (IntegralMixedIntegerProducerSpaceBits.coefficientPullback_FP _ HQ)).congr (funext fun z => ?_)
    simp only [Function.comp_apply,PrimitivePairBits.coefficient,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,RationalSubstitution.IntegerBits.mValue,
      IntegralMixedIntegerProducerSpaceBits.coefficientPullback,pairFst_pair,pairSnd_pair,taskPolynomial]
    rw [hp]

end LeanCanny.Algebra.IntegralMixedIntegerFamilyBits

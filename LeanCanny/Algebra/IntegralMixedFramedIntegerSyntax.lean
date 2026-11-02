/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedProducerDispatcher
public import LeanCanny.Algebra.IntegralMixedIntegerProducerOriginalSource
public import LeanCanny.ETR.IntegerUnivariateTermSource
/-! # Literal saved-birth integer syntax supplies the framed producer leaves

The word writer is queried at the full saved key, including its birth and
context. Pointwise polynomial transport identifies the actual creating integer
instruction. Its exact degree is computed in space; no degree/leading FP cost
or interpreted-history evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedIntegerSyntaxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

theorem original_of_word (P : Parameters) (a : Access P) (p : List Bool → Polynomial ℤ)
    (word : List Bool → List Bool) (hw : word∈FP)
    (hp : ∀ key, ETR.IntegerUnivariateTermSource.polynomial word key=p key) :
    IntegralMixedIntegerFamilyBits.Original P p where
  degree := by
    have E := ETR.IntegerUnivariateTermSource.degree_evaluator word hw
    refine (E.precompose (IntegralMixedVirtualTaskBits.saved P) (IntegralMixedVirtualTaskBits.saved_FP P a)).congr
      (funext fun q => ?_)
    change BinaryNatCode.encode (ETR.IntegerUnivariateTermSource.polynomial word (IntegralMixedVirtualTaskBits.saved P q)).natDegree=
      BinaryNatCode.encode (p (IntegralMixedVirtualTaskBits.saved P q)).natDegree
    rw [hp]
  coefficient := by
    have E := ETR.IntegerUnivariateTermSource.coefficient_evaluator word hw
    refine (E.precompose (IntegralMixedIntegerProducerSpaceBits.coefficientPullback (IntegralMixedVirtualTaskBits.saved P))
      (IntegralMixedIntegerProducerSpaceBits.coefficientPullback_FP _ (IntegralMixedVirtualTaskBits.saved_FP P a))).congr
      (funext fun z => ?_)
    simp only [Function.comp_apply,PrimitivePairBits.coefficient,RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree,RationalSubstitution.IntegerBits.mValue,
      IntegralMixedIntegerProducerSpaceBits.coefficientPullback,pairFst_pair,pairSnd_pair,
      IntegralMixedIntegerFamilyBits.taskPolynomial]
    rw [hp]

theorem original (P : Parameters) (a : Access P) (D : Plan P)
    (word : List Bool → List Bool) (hw : word∈FP)
    (hp : ∀ key, ETR.IntegerUnivariateTermSource.polynomial word key=IntegralMixedFramedIntegerBits.polynomial P D key) :
    IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P D) :=
  original_of_word P a _ word hw hp

noncomputable def controls (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
    (word : List Bool → List Bool) (hw : word∈FP)
    (hp : ∀ key, ETR.IntegerUnivariateTermSource.polynomial word key=IntegralMixedFramedIntegerBits.polynomial P D key) :
    IntegralMixedFramedProducerBits.Controls P D H where
  tables := T
  native := ht
  represents := hr
  integer := original P a D word hw hp

end LeanCanny.Algebra.IntegralMixedFramedIntegerSyntaxBits

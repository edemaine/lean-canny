/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTermBounds
public import LeanCanny.Encoding.IntegralMixedMarkedPointTest
/-! # The literal regularity and mark queries over the formal radius -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordMarkedQueries
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def word (n:List Bool→ℕ) (t:List Bool→LeanCanny.ETR.Term) (marked:Bool):List Bool→List Bool:=
  if marked then IntegralMixedMarkedPointTest.markWord n t else IntegralMixedMarkedPointTest.regularWord n t

private theorem native_planned (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C:List Bool→ℕ) (key:List Bool) (w:List Bool→List Bool):
    HEq (MvPolynomial.rename
      (IntegralFramedPhysicalSquare.sampler (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key).scalar
      (IntegralMixedFramedBankTermBits.polynomial (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) w key))
      (MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
        (IntegralMixedFramedBankTermBits.polynomial P D H w key)):=HEq.rfl

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

include hn ht in
theorem word_FP (marked:Bool):word n t marked∈FP:=by
  cases marked
  · exact IntegralMixedMarkedPointTest.regularWord_FP hn ht
  · exact IntegralMixedMarkedPointTest.markWord_FP hn ht

theorem literal_term (marked:Bool) (ctx:List Bool):
    CoefficientMarkedRecordTermQuery.termSyntax (word n t marked) ctx=
      if marked then
        LeanCanny.ETR.BoundedMarkedParameterTerm.mark
          (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)) (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx)
      else LeanCanny.ETR.BoundedMarkedParameterTerm.regular
          (t (IntegralMixedAuxiliaryMarkedIntegerSource.original ctx)) (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx)
          (IntegralMixedMarkedPointTest.degree t ctx):=by
  cases marked <;> exact LeanCanny.ETR.TermView.term_toBits _

noncomputable def polynomial (marked:Bool) (ctx:List Bool) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):=
  CoefficientMarkedRecordTermQuery.polynomial hn ht ha (word n t marked) ctx k hk

attribute [local irreducible] polynomial word IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedBankTermBits.polynomial IntegralFramedPhysicalSquare.sampler
  IntegralMixedSourceIntegerRecordAppend.plan

theorem specializes (marked:Bool) (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha marked ctx k hk))
      (MvPolynomial.rename
        (IntegralFramedPhysicalSquare.sampler (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
          (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
          (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
          (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).scalar
        (IntegralMixedFramedBankTermBits.polynomial (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
          (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
          (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
          (word n t marked) (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))):=
by
  unfold polynomial
  exact (CoefficientMarkedRecordTermQuery.polynomial_specialize hn ht ha (word n t marked) ctx R k hk aux hlarge).trans
    (native_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
      (fun _=>3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
      (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) (word n t marked)).symm

theorem coefficient_degree_mass (marked:Bool) (ctx:List Bool) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx)
    (e:Fin (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk).dimension→₀ ℕ):
    ((polynomial hn ht ha marked ctx k hk).coeff e).natDegree≤
        CoefficientMarkedRecordTermQuery.slope hn ht ha (word n t marked) ctx ∧
      coefficientMass ((polynomial hn ht ha marked ctx k hk).coeff e)≤
        2^CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha (word n t marked) ctx:=
by
  unfold polynomial
  exact CoefficientMarkedRecordTermQuery.coefficient_degree_mass hn ht ha (word n t marked) ctx k hk e

theorem coefficientBudget_binary (marked:Bool):BinaryFn (CoefficientMarkedRecordTermQuery.coefficientBudget hn ht ha (word n t marked)):=
  CoefficientMarkedRecordTermQuery.coefficientBudget_binary hn ht ha (word n t marked) (word_FP hn ht marked)

end LeanCanny.Encoding.CoefficientMarkedRecordMarkedQueries

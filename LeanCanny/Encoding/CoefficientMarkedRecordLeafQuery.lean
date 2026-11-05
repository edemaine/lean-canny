/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankLeafQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordTermQuery
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusDegree
/-! # Formal original leaves at the actual saved-prefix physical columns -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def sourceKey (ctx:List Bool) (i:ℕ):List Bool:=pair ctx (BinaryNatCode.encode i)

private theorem map_of_arguments {R S:Type*} [CommRing R] [CommRing S]
    (φ:R→+*S) (A:CoefficientBankTermQuery.Arguments R) (B:CoefficientBankTermQuery.Arguments S)
    (hA:A.map φ=B) (p:Polynomial R) (q:Polynomial S) (hp:p.map φ=q)
    (D E i:ℕ) (hD:D=E):
    HEq (MvPolynomial.map φ (CoefficientBankLeafQuery.polynomial A p D i))
      (CoefficientBankLeafQuery.polynomial B q E i):=by
  have HM:=CoefficientBankLeafQuery.polynomial_map φ A p D i
  have HA:=CoefficientBankLeafQuery.polynomial_heq_of_eq _ _ hA (p.map φ) D i
  have HQ:=congrArg₂ (fun p d=>CoefficientBankLeafQuery.polynomial B p d i) hp hD
  exact (heq_of_eq HM).trans (HA.trans (heq_of_eq HQ))

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def degree (ctx:List Bool) (i:ℕ):ℕ:=
  (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha (fun _=>0)).degree (sourceKey ctx i)

/-- This is the advertised source bound, not a replaced trailing/actual degree. -/
theorem degree_native (ctx:List Bool) (R:List Bool→ℕ) (i:ℕ):
    degree hn ht ha ctx i=(IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).degree (sourceKey ctx i):=rfl

noncomputable def polynomial (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (i:ℕ):=
  CoefficientBankLeafQuery.polynomial (CoefficientMarkedRecordTermQuery.arguments hn ht ha ctx k hk)
    (IntegralMixedAuxiliaryMarkedRadiusModel.polynomial hn ht ha (sourceKey ctx i)) (2*degree hn ht ha ctx i) i

attribute [local irreducible] CoefficientBankTermQuery.ofSnapshot IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan

noncomputable def nativeArguments (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool):
    CoefficientBankTermQuery.Arguments ℤ:=
  CoefficientBankTermQuery.ofSnapshot (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)
    (IntegralFramedPhysicalSquare.count (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux))
    (IntegralFramedPhysicalSquare.sampler (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
      (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux)).scalar

noncomputable def nativePolynomial (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool) (i:ℕ):=
  CoefficientBankLeafQuery.polynomial (nativeArguments hn ht ha ctx R k aux)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial (sourceKey ctx i))
    (2*(IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).degree (sourceKey ctx i)) i

attribute [local irreducible] polynomial nativePolynomial nativeArguments
  CoefficientMarkedRecordTermQuery.arguments CoefficientBankLeafQuery.polynomial

theorem specializes (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool) (i:ℕ)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha ctx k hk i))
      (nativePolynomial hn ht ha ctx R k aux i):=by
  have HA:=CoefficientMarkedRecordTermQuery.arguments_specialize hn ht ha ctx R k hk aux hlarge
  have HP:=IntegralMixedAuxiliaryMarkedRadiusModel.polynomial_map_eval hn ht ha R (sourceKey ctx i)
  simp only [sourceKey,pairFst_pair] at HP
  have HD:=congrArg (2*·) (degree_native hn ht ha ctx R i)
  unfold polynomial nativePolynomial nativeArguments
  exact map_of_arguments (evalRingHom ((2:ℤ)^R ctx)) _ _ HA _ _ HP _ _ i HD

/-- The native side is literally the installed univariate rational-point recipe. -/
theorem native_recipe (ctx:List Bool) (R:List Bool→ℕ) (k:ℕ) (aux:List Bool) (i:ℕ)
    (hi:i<(nativeArguments hn ht ha ctx R k aux).birth):
    nativePolynomial hn ht ha ctx R k aux i=
      ((IntegerPolynomialRationalPointSource.source (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
        (CoefficientBankLeafQuery.scalars (nativeArguments hn ht ha ctx R k aux) i)
        (fun _=>UniformIntegralPowerSchedule.birth (nativeArguments hn ht ha ctx R k aux).horizon
          (2^(nativeArguments hn ht ha ctx R k aux).width) i)).polynomial (sourceKey ctx i)).toMvPolynomial
          ((nativeArguments hn ht ha ctx R k aux).column
            ⟨(nativeArguments hn ht ha ctx R k aux).birth-1-i,by omega⟩):=
by
  unfold nativePolynomial
  exact CoefficientBankLeafQuery.polynomial_native _
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R) (sourceKey ctx i) i hi

end LeanCanny.Encoding.CoefficientMarkedRecordLeafQuery

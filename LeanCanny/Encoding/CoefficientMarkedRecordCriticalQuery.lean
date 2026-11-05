/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientCriticalCorrelationQuery
public import LeanCanny.Encoding.CoefficientMarkedRecordCriticalMetadata
/-! # The actual full-physical critical correlation query over the radius parameter -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCriticalQuery
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem denominator_planned (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C:List Bool→ℕ) (key:List Bool) (i:ℕ):
    IntegralMixedFramedCriticalGuardBits.atKey
      (IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
        (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
        (IntegralMixedFramedNormalizationBits.plannedData P D H L F C)) key i=
      IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedFramedHistoryFamilyBits.family P D H) key i:=rfl

private theorem native_heq (P:IntegralCriticalHistoryTask.Parameters)
    (D:IntegralMixedFramedHistoryFamilyBits.Plan P) (H:IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T:IntegralMixedHeaderTablesBits.Tables) (key:List Bool) (stage:ℕ):
    HEq (CoefficientCriticalCorrelationQuery.polynomial
      (CoefficientCriticalCorrelationQuery.nativeMetadata P T key stage)
      (IntegralMixedFramedCriticalGuardBits.atKey (IntegralMixedFramedHistoryFamilyBits.family P D H) key
        (CoefficientCriticalCorrelationQuery.nativeMetadata P T key stage).age))
      (IntegralMixedFramedCriticalGuardBits.polynomial P D H T (fun _=>key) (fun _=>stage) []):=
  heq_of_eq (CoefficientCriticalCorrelationQuery.polynomial_native P D H T key stage)

private theorem polynomial_transport (M N:CoefficientCriticalCorrelationQuery.Metadata) (hM:M=N)
    (d e:ℤ) (hd:d=e):
    HEq (CoefficientCriticalCorrelationQuery.polynomial M d) (CoefficientCriticalCorrelationQuery.polynomial N e):=
  (CoefficientCriticalCorrelationQuery.polynomial_heq_of_eq M N hM d).trans
    (heq_of_eq (congrArg (CoefficientCriticalCorrelationQuery.polynomial N) hd))

variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def metadata (ctx:List Bool) (k:ℕ) (aux:List Bool) (stage:ℕ):
    CoefficientCriticalCorrelationQuery.Metadata:=
  CoefficientCriticalCorrelationQuery.nativeMetadata (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) stage

/-- Count, age, both raw columns, both powers and Active are all literal. -/
theorem metadata_eq (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ) (aux:List Bool) (stage:ℕ):
    metadata hn ht ha ctx k aux stage=
      CoefficientCriticalCorrelationQuery.nativeMetadata
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) stage:=by
  have HT:=congrArg (fun T=>CoefficientCriticalCorrelationQuery.nativeMetadata
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR) T
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) stage)
      (CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR)
  have HP:=CoefficientCriticalCorrelationQuery.nativeMetadata_planned
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) (fun _=>3)
    (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) stage
  exact (HT.trans HP).symm

theorem header_eq {R:List Bool→ℕ} (hR:BinaryFn R) (key:List Bool) (stage:ℕ):
    IntegralMixedFramedCriticalGuardBits.header (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
      (fun _=>key) (fun _=>stage) []=
      IntegralMixedFramedCriticalGuardBits.header (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
        (fun _=>key) (fun _=>stage) []:=
  congrArg (fun T=>IntegralMixedFramedCriticalGuardBits.header T (fun _=>key) (fun _=>stage) [])
    (CoefficientMarkedRecordCriticalMetadata.tables_eq hn ht ha hR)

noncomputable def polynomial (ctx:List Bool) (k:ℕ) (aux:List Bool) (stage:ℕ):
    MvPolynomial (Fin (metadata hn ht ha ctx k aux stage).count) ℤ[X]:=
  CoefficientCriticalCorrelationQuery.polynomial (metadata hn ht ha ctx k aux stage)
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k (metadata hn ht ha ctx k aux stage).age)

attribute [local irreducible] metadata polynomial CoefficientCriticalCorrelationQuery.nativeMetadata
  CoefficientCriticalCorrelationQuery.polynomial IntegralMixedFramedCriticalGuardBits.atKey
  IntegralMixedFramedHistoryFamilyBits.family IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedAuxiliaryMarkedIntegerSource.candidate IntegralMixedAuxiliaryCandidate.sourceInput
  IntegralMixedAuxiliaryCandidate.source IntegralMixedAuxiliaryMarkedIntegerSource.oldKey

theorem specializes (ctx:List Bool) {R:List Bool→ℕ} (hR:BinaryFn R) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (aux:List Bool) (stage:ℕ)
    (hlarge:CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx≤R ctx):
    HEq (MvPolynomial.map (evalRingHom ((2:ℤ)^R ctx)) (polynomial hn ht ha ctx k aux stage))
      (IntegralMixedFramedCriticalGuardBits.polynomial
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
        (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
        (IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false)
        (fun _=>CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux) (fun _=>stage) []):=by
  let P:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR
  let D:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR
  let H:=IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR
  let T:=IntegralMixedPhysicalMarkedPlan.tables hn ht ha hR false
  let key:=CoefficientMarkedRecordRowLayout.key (n:=n) ctx k aux
  let M:=metadata hn ht ha ctx k aux stage
  let N:=CoefficientCriticalCorrelationQuery.nativeMetadata P T key stage
  have HMeta:M=N:=metadata_eq hn ht ha ctx hR k aux stage
  have HDBase:=CoefficientMarkedRecordBankDenominator.specializes hn ht ha ctx R k hk aux hlarge M.age
  have HDPlan:=denominator_planned (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R)
    (fun _=>3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) key M.age
  have HDAge:=congrArg (IntegralMixedFramedCriticalGuardBits.atKey
    (IntegralMixedFramedHistoryFamilyBits.family P D H) key) (congrArg CoefficientCriticalCorrelationQuery.Metadata.age HMeta)
  have HD:=HDBase.trans (HDPlan.symm.trans HDAge)
  have HM:=CoefficientCriticalCorrelationQuery.polynomial_map (evalRingHom ((2:ℤ)^R ctx)) M
    (CoefficientMarkedRecordBankDenominator.polynomial hn ht ha ctx k M.age)
  have HE:=polynomial_transport M N HMeta _ _ HD
  unfold polynomial
  exact (heq_of_eq HM).trans (HE.trans (native_heq P D H T key stage))

noncomputable def coefficientBudget (ctx:List Bool):ℕ:=
  CoefficientMarkedRecordBankDenominator.coefficientBudget hn ht ha ctx+1

theorem coefficientBudget_binary:BinaryFn (coefficientBudget hn ht ha):=
  (CoefficientMarkedRecordBankDenominator.coefficientBudget_binary hn ht ha).add (BinaryFn.const 1)

theorem coefficient_degree_mass (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx)
    (aux:List Bool) (stage:ℕ) (e:Fin (metadata hn ht ha ctx k aux stage).count→₀ ℕ):
    ((polynomial hn ht ha ctx k aux stage).coeff e).natDegree≤
        IntegralMixedAuxiliaryMarkedRecordRadiusHeight.bankSlope hn ht ha ctx ∧
      coefficientMass ((polynomial hn ht ha ctx k aux stage).coeff e)≤2^coefficientBudget hn ht ha ctx:=by
  obtain ⟨HD,HM⟩:=CoefficientMarkedRecordBankDenominator.degree_mass hn ht ha ctx k hk
    (metadata hn ht ha ctx k aux stage).age
  unfold polynomial
  exact CoefficientCriticalCorrelationQuery.coefficient_degree_mass _ _ _ _ HD HM e

end LeanCanny.Encoding.CoefficientMarkedRecordCriticalQuery

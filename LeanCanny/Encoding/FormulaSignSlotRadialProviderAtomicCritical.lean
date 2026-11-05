/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSample
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardScan
/-! # All creating critical correlations use one provider full word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem guard_count_at (B : IntegralFramedBankQuery.Bank)
    (T : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T) (c d : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count B.parameters T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) (pair c d)=
        (IntegralFramedPhysicalBankTerm.input B).count c := by
  change _=IntegralMixedFramedPhysicalIndex.arity
    (IntegralMixedFramedHistoryFamilyBits.commands B.parameters B.plan (B.key c))
  have H := IntegralMixedFramedCriticalGuardBits.count_actual B.parameters B.plan B.data T hr
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key) (pair c d)
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum B.key (pair c d)=B.key c :=
    congrArg B.key (pairFst_pair c d)
  exact H.trans (congrArg (fun k => IntegralMixedFramedPhysicalIndex.arity
    (IntegralMixedFramedHistoryFamilyBits.commands B.parameters B.plan k)) HK)

theorem critical_count (c d : List Bool) : IntegralMixedFramedCriticalGuardBits.count
    FormulaSignSlotRadialProviderRecordPlan.bank.parameters FormulaSignSlotRadialProviderRecordPlan.tables
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum FormulaSignSlotRadialProviderRecordPlan.bank.key)
    (pair c d)=input.count c :=
  guard_count_at FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables
    bank_represents c d

noncomputable def criticalLanguage := IntegralFramedPhysicalCriticalGuardScan.language input
  FormulaSignSlotRadialProviderRecordPlan.bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank.plan
  FormulaSignSlotRadialProviderRecordPlan.bank.data FormulaSignSlotRadialProviderRecordPlan.tables
  FormulaSignSlotRadialProviderRecordPlan.bank.nodes FormulaSignSlotRadialProviderRecordPlan.bank.factor
  FormulaSignSlotRadialProviderRecordPlan.bank.seed FormulaSignSlotRadialProviderRecordPlan.bank.bounds
  FormulaSignSlotRadialProviderRecordPlan.bank.key critical_count
theorem critical_decider : SpaceDecider criticalLanguage := by
  let B := FormulaSignSlotRadialProviderRecordPlan.bank
  let A := FormulaSignSlotRadialProviderRecordPlan.bank_access
  exact IntegralFramedPhysicalCriticalGuardScan.decider input B.parameters B.plan B.data
    FormulaSignSlotRadialProviderRecordPlan.tables B.nodes B.factor B.seed B.bounds B.key critical_count
    input_access A.parameters FormulaSignSlotRadialProviderRecordPlan.tables_native A.liftedData
    A.controls A.bounds A.nodes A.factor A.seed A.key

noncomputable def CriticalScan (q : List Bool) := sampleQuery q∈criticalLanguage
theorem criticalScan_decider : SpaceDecider {q | CriticalScan q} :=
  critical_decider.precompose sampleQuery sampleQuery_FP
theorem criticalScan_full_valid (q : List Bool) (h : CriticalScan q) : FullValid q := by
  simpa only [FullValid,sampleQuery,pairFst_pair,pairSnd_pair] using h.1
theorem criticalScan_PSPACE : {q | CriticalScan q}∈PSPACE := criticalScan_decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic

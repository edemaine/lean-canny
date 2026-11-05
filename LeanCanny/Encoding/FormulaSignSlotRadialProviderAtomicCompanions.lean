/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicCritical
public import LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
/-! # Latest companion captures at the actual source-aware full point

Creating births are test data. Every coordinate equality and selected
correlation keeps the same provider record context and complete own word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Companions
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (input input_access critical_count)
open IntegralMixedPhysicalPointCompanionScan (Wellformed wellformed_FP anchorQuery anchorQuery_FP
  first first_unary number number_unary coordinateQuery coordinateQuery_FP correlationQuery correlationQuery_FP)
open IntegralMixedPhysicalPointEquality (left left_unary right right_unary coordinate coordinate_binary
  context context_FP Wellformed wellformed_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A" => FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable def pointValue := IntegralFramedPhysicalPointEqualityTest.value input P T (B).key
  left right coordinate critical_count
theorem pointValue_evaluator : SpaceFunction pointValue :=
  IntegralFramedPhysicalPointEqualityTest.evaluator input P T (B).key left right coordinate critical_count
    input_access (A).parameters FormulaSignSlotRadialProviderRecordPlan.tables_native (A).key
    left_unary right_unary coordinate_binary
noncomputable def PointAdmissible (q : List Bool) := IntegralMixedFramedPointEqualityBits.Admissible P T
  (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) left right coordinate (IntegralMixedPhysicalPointEquality.context q)
theorem pointAdmissible_FP : FPPred PointAdmissible :=
  (IntegralMixedFramedPointEqualityBits.admissible_FP P T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key) left right coordinate (A).parameters
    FormulaSignSlotRadialProviderRecordPlan.tables_native
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum_FP (B).key (A).key)
    left_unary right_unary coordinate_binary).comp IntegralMixedPhysicalPointEquality.context_FP
noncomputable def PointAccepted (q : List Bool) := IntegralMixedPhysicalPointEquality.Wellformed q ∧
  PointAdmissible q ∧ pointValue q=InfinitesimalSign.encode 0
theorem pointAccepted_evaluator : SpaceFunction (fun q => [decide (PointAccepted q)]) := by
  have EG := SpaceFunction.ofFP _ (IntegralMixedPhysicalPointEquality.wellformed_FP.and pointAdmissible_FP).flag_mem_FP
  have EZ := pointValue_evaluator.postcompose (fun v => [decide (v=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  exact (EG.andFlags EZ).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [PointAccepted,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc])

noncomputable def dimension (z : List Bool) := (P).ambient (pairFst ((B).key (pairFst (pairFst z))))+1
theorem dimension_unary : UnaryFn dimension := by
  have HZ : (fun z : List Bool => pairFst (pairFst z)) ∈ FP := by polytime
  exact ((A).parameters.ambient.comp
    (mem_FP_comp (mem_FP_comp HZ (A).key) pairFst_mem_FP)).add (UnaryFn.const 1)
noncomputable def Grammar (z : List Bool) := IntegralMixedPhysicalPointCompanionScan.Wellformed z ∧
  IntegralMixedFramedCriticalGuardBits.Active P T (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
    IntegralFramedPhysicalCriticalGuardScan.stage (anchorQuery z) ∧
  IntegralMixedPhysicalPointCompanionScan.first z+number z≤IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (pairFst (pairFst z)))
theorem grammar_FP : FPPred Grammar := by
  have HA := (IntegralMixedFramedCriticalGuardBits.active_FP P (A).parameters T
    FormulaSignSlotRadialProviderRecordPlan.tables_native (IntegralFramedPhysicalCriticalGuardTest.keyDatum (B).key)
    IntegralFramedPhysicalCriticalGuardScan.stage
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum_FP (B).key (A).key)
    IntegralFramedPhysicalCriticalGuardScan.stage_unary).comp anchorQuery_FP
  have HP : UnaryFn (fun z => IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (pairFst (pairFst z)))) :=
    (IntegralMixedFullHistoryFamilyBits.prefix_unary P (A).parameters).comp
      (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (A).key)
  exact IntegralMixedPhysicalPointCompanionScan.wellformed_FP.and
    (HA.and ((BinaryFn.ofUnary (IntegralMixedPhysicalPointCompanionScan.first_unary.add number_unary)).le (BinaryFn.ofUnary HP)))

noncomputable def correlation := IntegralFramedPhysicalCriticalGuardTest.value input P (B).plan (B).data T
  (B).nodes (B).factor (B).seed (B).bounds (B).key IntegralFramedPhysicalCriticalGuardScan.stage critical_count ∘correlationQuery
theorem correlation_evaluator : SpaceFunction correlation := by
  unfold correlation
  exact (IntegralFramedPhysicalCriticalGuardTest.evaluator input P (B).plan (B).data T
    (B).nodes (B).factor (B).seed (B).bounds (B).key IntegralFramedPhysicalCriticalGuardScan.stage critical_count
    input_access (A).parameters FormulaSignSlotRadialProviderRecordPlan.tables_native (A).liftedData
    (A).controls (A).bounds (A).nodes (A).factor (A).seed (A).key
    IntegralFramedPhysicalCriticalGuardScan.stage_unary).precompose correlationQuery correlationQuery_FP
noncomputable def holds (z : List Bool) := ∀j<number z,
  (∀i<dimension z, PointAccepted
    (coordinateQuery (pair (pair z (List.replicate j true)) (List.replicate i true)))) ∧
  correlation (pair z (List.replicate j true))=InfinitesimalSign.encode 0
theorem holds_evaluator : SpaceFunction (fun z => [decide (holds z)]) := by
  have EC := pointAccepted_evaluator.precompose coordinateQuery coordinateQuery_FP
  have EI := EC.forall_unary (dimension_unary.comp pairFst_mem_FP)
  have ES := correlation_evaluator.postcompose (fun v => [decide (v=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  exact ((EI.andFlags ES).forall_unary number_unary).congr (funext fun z => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])
noncomputable def language : Language := {z | SquareSampleCompleteVertices.Valid input
  (pairFst (pairFst z)) (pairSnd (pairFst z)) ∧ Grammar z ∧ holds z}
theorem decider : SpaceDecider language := by
  have EV := ((SquareSampleCompleteVertices.decider input_access).precompose pairFst pairFst_mem_FP).flagEvaluator
  have EG := SpaceFunction.ofFP _ grammar_FP.flag_mem_FP
  apply (EV.andFlags (EG.andFlags holds_evaluator)).decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Companions

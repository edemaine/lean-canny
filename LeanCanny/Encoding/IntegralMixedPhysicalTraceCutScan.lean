/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuards
public import LeanCanny.Encoding.IntegralMixedPhysicalGuardScan
public import LeanCanny.Encoding.IntegralFramedTraceCutScan
public import LeanCanny.Encoding.IntegralFramedTraceCutOriginalCount

/-! # Every chronological creating cut uses the same full replay word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native controls)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralFramedTraceCutScan (stagePacket stageQuery stageQuery_FP)
open IntegralMixedPhysicalTraceCutGuards (Guards)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem marked_length (ctx : List Bool) :
    ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R).rules ctx).length=
      IntegralMixedCausalRecordPlanBits.count ctx+(IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) :=by
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.plan
  apply IntegralMixedSourceIntegerRecordAppend.script_length

theorem outer_length (ctx : List Bool) :
    ((IntegralMixedAuxiliaryOuterRecordPlan.plan hn ht ha R).rules ctx).length=
      IntegralMixedCausalRecordPlanBits.count ctx+(IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+10) :=by
  unfold IntegralMixedAuxiliaryOuterRecordPlan.plan
  apply IntegralMixedSourceIntegerRecordAppend.script_length

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedAuxiliaryMarkedRecordPlan.plan
  IntegralMixedAuxiliaryMarkedRecordPlan.data IntegralMixedAuxiliaryOuterRecordPlan.parameters
  IntegralMixedAuxiliaryOuterRecordPlan.plan IntegralMixedAuxiliaryOuterRecordPlan.data

noncomputable def count (q : List Bool) :=
  IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext (pairFst q))
theorem count_unary : UnaryFn (count hn ht ha hR outer) :=
  (IntegralMixedPhysicalReplayNew.count_unary hn ht ha hR outer).comp
    (mem_FP_comp pairFst_mem_FP IntegralMixedPhysicalMarkedTest.sampleContext_FP)

theorem count_eq_length (ctx w : List Bool) : count hn ht ha hR outer (pair ctx w)=
    IntegralFramedTraceCutMetadata.length (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan ctx :=by
  cases outer
  · change (IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (sampleContext (pairFst (pair ctx w))))).count=
        ((IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R).rules ctx).length
    rw [IntegralMixedAuxiliaryMarkedRecordPlan.bank_count,marked_length hn ht ha (R:=R)]
    simp only [IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,sampleContext,pairFst_pair]
    omega
  · change (IntegralMixedFramedBankSnapshotBits.atKey
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.certifiedData hn ht ha hR)
      (IntegralMixedAuxiliaryOuterRecordPlan.bankKey n (sampleContext (pairFst (pair ctx w))))).count=
        ((IntegralMixedAuxiliaryOuterRecordPlan.plan hn ht ha R).rules ctx).length
    rw [IntegralMixedAuxiliaryOuterRecordPlan.bank_count,outer_length hn ht ha (R:=R)]
    simp only [IntegralMixedAuxiliaryOuterRecordPlan.fullCount,sampleContext,pairFst_pair]
    omega

noncomputable def StageCut (b : List Bool) :=IntegralFramedTraceCutScan.StageCut
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan b
theorem stageCut_FP : FPPred (StageCut hn ht ha hR outer) :=
  IntegralFramedTraceCutScan.stageCut_FP (bank hn ht ha hR outer).parameters
    (native hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (controls hn ht ha hR outer).normalization

noncomputable def holds (q : List Bool) : Prop :=
  ∀j<count hn ht ha hR outer q,StageCut hn ht ha hR outer (stagePacket q j)→
    Guards hn ht ha hR outer (stagePacket q j)
noncomputable def language : Language :={q |
  SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext (pairFst q)) (pairSnd q) ∧
    holds hn ht ha hR outer q}

attribute [local irreducible] bank count StageCut

theorem holds_evaluator (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceFunction (fun q=>[decide (holds hn ht ha hR outer q)]) :=by
  have EG:=IntegralMixedPhysicalTraceCutGuards.evaluator hn ht ha hR outer ER
  have E:=SpaceFunction.branch (fun b=>decide (StageCut hn ht ha hR outer b))
    (stageCut_FP hn ht ha hR outer).flag_mem_FP EG (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  have EI : SpaceFunction (fun b=>[decide (StageCut hn ht ha hR outer b→Guards hn ht ha hR outer b)]) :=
    E.congr (by
      funext b
      by_cases HB:StageCut hn ht ha hR outer b <;>
        simp only [HB,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,
          true_implies,false_implies,decide_true])
  have EU:=(EI.precompose stageQuery stageQuery_FP).forall_unary (count_unary hn ht ha hR outer)
  exact EU.congr (by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,stageQuery,stagePacket,pairFst_pair,pairSnd_pair,
      List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceDecider (language hn ht ha hR outer) :=by
  have EV:=((SquareSampleCompleteVertices.decider
    (IntegralMixedPhysicalReplayThom.input_access hn ht ha hR outer ER)).precompose
      IntegralMixedPhysicalMarkedTest.leafQuery IntegralMixedPhysicalMarkedTest.leafQuery_FP).flagEvaluator
  have EU:=holds_evaluator hn ht ha hR outer ER
  apply (EV.andFlags EU).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    IntegralMixedPhysicalMarkedTest.leafQuery,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def relation : Language :={q |
  q∈IntegralMixedPhysicalGuardScan.relation hn ht ha hR outer ∧q∈language hn ht ha hR outer}

theorem relation_decider (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceDecider (relation hn ht ha hR outer) :=by
  have EC:=(IntegralMixedPhysicalGuardScan.relation_decider hn ht ha hR outer ER).flagEvaluator
  have ET:=(decider hn ht ha hR outer ER).flagEvaluator
  apply (EC.andFlags ET).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [relation,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem accepted_good (u label metadata w : List Bool)
    (h : pair (pair (pair u label) metadata) w∈relation hn ht ha hR outer) :
    LeanCanny.Connectivity.AuxiliaryCandidateComponentCover.Good hn ht ha u label :=
  IntegralMixedPhysicalReplayRelation.accepted_good hn ht ha hR outer u label metadata w h.1.1

theorem mem_PSPACE (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    relation hn ht ha hR outer∈PSPACE :=(relation_decider hn ht ha hR outer ER).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan

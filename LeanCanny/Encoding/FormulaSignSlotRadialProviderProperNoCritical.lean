/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalQuery
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # Native no-critical guard with independent prepared full and parent words

The prepared FULL word matches every older original quotient. A second
prepared PARENT word agrees with that full word through the existing joint
scan. The reserved child search is then the actual critical interval test.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def atomic (z : List Bool):=pairFst (pairFst z)
def fullWord (z : List Bool):=pairSnd (pairFst z)
def parentWord (z : List Bool):=pairSnd z
theorem atomic_FP : atomic∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem fullWord_FP : fullWord∈FP:=mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem parentWord_FP : parentWord∈FP:=pairSnd_mem_FP

noncomputable def critical (z : List Bool):=query (pair (atomic z) (parentWord z))
noncomputable def joint (z : List Bool):=pair (critical z) (fullWord z)
noncomputable def fields (z : List Bool):=FormulaSignSlotRadialProviderFieldEqualityList.packet
  (FormulaSignSlotRadialProviderAtomic.context (atomic z)) (FormulaSignSlotRadialProviderAtomic.word (atomic z))
  (context (atomic z)) (fullWord z)
  (IntegralMixedRoadmapBadProbePacket.matchTable (FormulaSignSlotRadialProviderAtomic.initial (atomic z))
    (IntegralMixedRoadmapProper.badPacket (atomic z)))

theorem critical_FP : critical∈FP:=mem_FP_comp (mem_FP_pair atomic_FP parentWord_FP) (query_FP)
theorem joint_FP : joint∈FP:=mem_FP_pair (critical_FP) fullWord_FP
theorem fields_FP : fields∈FP:=by
  have HC:=mem_FP_comp (f:=atomic) (g:=FormulaSignSlotRadialProviderAtomic.context) atomic_FP FormulaSignSlotRadialProviderAtomic.context_FP
  have HW:=mem_FP_comp (f:=atomic) (g:=FormulaSignSlotRadialProviderAtomic.word) atomic_FP FormulaSignSlotRadialProviderAtomic.word_FP
  have HP:=mem_FP_comp atomic_FP (context_FP)
  have HT:=IntegralMixedRoadmapBadProbePacket.matchTable_FP
    ((FormulaSignSlotRadialProviderAtomic.initial_unary).comp atomic_FP)
    (mem_FP_comp atomic_FP IntegralMixedRoadmapProper.badPacket_FP)
  exact mem_FP_pair (mem_FP_pair HC HW) (mem_FP_pair (mem_FP_pair HP fullWord_FP) HT)

noncomputable def Witness (z : List Bool):=FormulaSignSlotRadialProviderCriticalInterval.Guard (critical z) ∧
  SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderCriticalPrefixes.input false)
    (critical z) (parentWord z) ∧
  SquareSampleCompleteVertices.Valid (FormulaSignSlotRadialProviderCriticalPrefixes.input true)
    (critical z) (fullWord z) ∧
  fields z∈FormulaSignSlotRadialProviderFieldEqualityList.language ∧
  FormulaSignSlotRadialProviderCriticalBankEquality.agrees (joint z) ∧
  critical z∉FormulaSignSlotRadialProviderCriticalInterval.language

theorem witness_evaluator : SpaceFunction (fun z=>[decide (Witness z)]):=by
  have EG:=SpaceFunction.ofFP _ ((FormulaSignSlotRadialProviderCriticalInterval.guard_FP).comp (critical_FP)).flag_mem_FP
  have EP:=((SquareSampleCompleteVertices.decider (FormulaSignSlotRadialProviderCriticalPrefixes.access false)).precompose
    (fun z=>pair (critical z) (parentWord z)) (mem_FP_pair (critical_FP) parentWord_FP)).flagEvaluator
  have EF:=((SquareSampleCompleteVertices.decider (FormulaSignSlotRadialProviderCriticalPrefixes.access true)).precompose
    (fun z=>joint z) (joint_FP)).flagEvaluator
  have EM:=((FormulaSignSlotRadialProviderFieldEqualityList.decider).precompose _ (fields_FP)).flagEvaluator
  have EA:=(FormulaSignSlotRadialProviderCriticalBankEquality.scanEvaluator).precompose _ (joint_FP)
  have EN:=(((FormulaSignSlotRadialProviderCriticalInterval.decider).precompose _
    (critical_FP)).flagEvaluator).postcompose _
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact (EG.andFlags (EP.andFlags (EF.andFlags (EM.andFlags (EA.andFlags EN))))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Witness,Function.comp_apply,joint,Set.mem_preimage,SquareSampleCompleteVertices.language,
      Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq,id_eq])

noncomputable def fullWidth (q : List Bool):=SquareSampleCompleteVertices.width
  (FormulaSignSlotRadialProviderCriticalPrefixes.input true) (canonical q)
noncomputable def parentWidth (q : List Bool):=SquareSampleCompleteVertices.width
  (FormulaSignSlotRadialProviderCriticalPrefixes.input false) (canonical q)
theorem fullWidth_unary : UnaryFn (fullWidth):=
  (SquareSampleCompleteVertices.width_unary (FormulaSignSlotRadialProviderCriticalPrefixes.access true)).comp
    (canonical_FP)
theorem parentWidth_unary : UnaryFn (parentWidth):=
  (SquareSampleCompleteVertices.width_unary (FormulaSignSlotRadialProviderCriticalPrefixes.access false)).comp
    (canonical_FP)

noncomputable def NoCritical (q : List Bool):=∃wF : List Bool,wF.length=fullWidth q∧
  ∃wP : List Bool,wP.length=parentWidth q∧Witness (pair (pair q wF) wP)
theorem noCritical_evaluator : SpaceFunction (fun q=>[decide (NoCritical q)]):=by
  have E:=((witness_evaluator).exists_words ((parentWidth_unary).comp pairFst_mem_FP)).exists_words
    (fullWidth_unary)
  exact E.congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [NoCritical,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCritical

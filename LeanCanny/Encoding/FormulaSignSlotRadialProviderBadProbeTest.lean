/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native correlated witnesses to failure of a reserved interval probe

The base full word and a freshly sampled prepared-root word agree on every
old scalar producer. The last producer belongs only to the new probe. The
factor guard checks validity and the exact specialized degree. Geometric
identification with the whole ordinary bad set is a separate theorem.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "A" => IntegralFramedBankQuery.Access.parameters (FormulaSignSlotRadialProviderRecordPlan.bank_access)
local notation "S" => FormulaSignSlotRadialProviderAtomic.input

noncomputable def dimension (q : List Bool):=(P).ambient (IntegralMixedRoadmapBadProbePacket.root (pairFst q))
noncomputable def initial (q : List Bool):=dimension q+5
noncomputable def width (q : List Bool):=(P).width (IntegralMixedRoadmapBadProbePacket.root (pairFst q))
theorem dimension_unary : UnaryFn (dimension):=
  (A).ambient.comp (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.root_FP)
theorem initial_unary : UnaryFn (initial):=(dimension_unary).add (UnaryFn.const 5)
theorem width_unary : UnaryFn (width):=
  (A).width.comp (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.root_FP)

noncomputable def intervalContext (q : List Bool):=
  IntegralMixedRoadmapBadProbePacket.intervalContext (dimension q) (initial q) q
noncomputable def intervalPacket (z : List Bool):=pair (intervalContext (pairFst z)) (pairSnd z)
noncomputable def fieldPacket (z : List Bool):=FormulaSignSlotRadialProviderFieldEqualityList.packet
  (pair (IntegralMixedRoadmapBadProbePacket.root (pairFst (pairFst z))) []) (IntegralMixedRoadmapBadProbePacket.word (pairFst (pairFst z)))
  (pair (IntegralMixedRoadmapBadProbePacket.preparedRoot (dimension (pairFst z)) (pairFst z)) []) (pairSnd z)
  (IntegralMixedRoadmapBadProbePacket.matchTable (initial (pairFst z)) (pairFst (pairFst z)))

theorem intervalContext_FP : intervalContext∈FP:=
  IntegralMixedRoadmapBadProbePacket.intervalContext_FP (dimension_unary) (initial_unary)
theorem intervalPacket_FP : intervalPacket∈FP:=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (intervalContext_FP)) pairSnd_mem_FP

theorem fieldPacket_FP : fieldPacket∈FP:=by
  have HQ:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HC:=mem_FP_pair (mem_FP_comp HQ IntegralMixedRoadmapBadProbePacket.root_FP) (constFn_mem_FP [])
  have HR:=mem_FP_comp pairFst_mem_FP
    (IntegralMixedRoadmapBadProbePacket.preparedRoot_FP (dimension_unary))
  exact mem_FP_pair (mem_FP_pair HC (mem_FP_comp (g:=IntegralMixedRoadmapBadProbePacket.word) HQ IntegralMixedRoadmapBadProbePacket.word_FP))
    (mem_FP_pair (mem_FP_pair (mem_FP_pair HR (constFn_mem_FP [])) pairSnd_mem_FP)
      (IntegralMixedRoadmapBadProbePacket.matchTable_FP ((initial_unary).comp pairFst_mem_FP) HQ))

noncomputable def Witness (z : List Bool) : Prop:=
  IntegralMixedRoadmapBadProbePacket.HintGood (dimension (pairFst z)) (initial (pairFst z))
    (width (pairFst z)) (pairFst z) ∧
  fieldPacket z∈FormulaSignSlotRadialProviderFieldEqualityList.language ∧
  SquareSampleCompleteVertices.Valid S (intervalContext (pairFst z)) (pairSnd z) ∧
  FormulaSignSlotRadialProviderCutInterval.Bounds (intervalPacket z) ∧
  FormulaSignSlotRadialProviderCutInterval.Guards (intervalPacket z) ∧
  intervalPacket z∉FormulaSignSlotRadialProviderCutInterval.language

noncomputable def language : Language:={z | Witness z}

theorem evaluator : SpaceFunction (fun z=>[decide (Witness z)]):=by
  have EH:=SpaceFunction.ofFP _ ((IntegralMixedRoadmapBadProbePacket.hintGood_FP
    (dimension_unary) (initial_unary) (width_unary)).comp
      pairFst_mem_FP).flag_mem_FP
  have EF:=((FormulaSignSlotRadialProviderFieldEqualityList.decider).precompose _ (fieldPacket_FP)).flagEvaluator
  have EV:=((SquareSampleCompleteVertices.decider
    (FormulaSignSlotRadialProviderAtomic.input_access)).precompose _
      (intervalPacket_FP)).flagEvaluator
  have EB:=SpaceFunction.ofFP _ (((FormulaSignSlotRadialProviderCutInterval.bounds_FP).comp
    (intervalPacket_FP))).flag_mem_FP
  have EG:=(FormulaSignSlotRadialProviderCutInterval.guards_evaluator).precompose _
    (intervalPacket_FP)
  have EN:=(((FormulaSignSlotRadialProviderCutInterval.decider).precompose _ (intervalPacket_FP)).flagEvaluator).postcompose _
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact (EH.andFlags (EF.andFlags (EV.andFlags (EB.andFlags (EG.andFlags EN))))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,id_eq,pairFst_pair,pairSnd_pair,Witness,Set.mem_preimage,SquareSampleCompleteVertices.language,intervalPacket,
      Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language):=by
  apply (evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,List.cons.injEq,and_true,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE:=(decider).mem_PSPACE

noncomputable def probeWordWidth (q : List Bool):=SquareSampleCompleteVertices.width S (intervalContext q)
theorem probeWordWidth_unary : UnaryFn (probeWordWidth):=
  (SquareSampleCompleteVertices.width_unary (FormulaSignSlotRadialProviderAtomic.input_access)).comp
    (intervalContext_FP)
noncomputable def HasWitness (q : List Bool):=∃w : List Bool,
  w.length=probeWordWidth q ∧ Witness (pair q w)
theorem witness_word_length (q w : List Bool) (h : Witness (pair q w)) :
    w.length=probeWordWidth q :=by
  have HV : SquareSampleCompleteVertices.Valid S (intervalContext q) w:=by
    simpa only [pairFst_pair,pairSnd_pair] using h.2.2.1
  exact (Classical.choose HV).1

theorem hasWitness_iff (q : List Bool) :
    HasWitness q ↔ ∃w : List Bool,Witness (pair q w) :=by
  constructor
  · rintro ⟨w,_,h⟩
    exact ⟨w,h⟩
  · rintro ⟨w,h⟩
    exact ⟨w,witness_word_length q w h,h⟩

theorem hasWitness_evaluator : SpaceFunction (fun q=>[decide (HasWitness q)]):=by
  exact ((evaluator).exists_words (probeWordWidth_unary)).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [HasWitness,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeTest

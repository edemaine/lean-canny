/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNearNative
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList

/-! # One coordinate certificate keeps two own-root full words

The ordinary word controls Near; the mean-centered word controls rank at
eta zero. Each is matched to ALL original older retained quotients.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (key ordinary mean rank : List Bool):=pair key (pair ordinary (pair mean rank))
def key (u : List Bool):=pairFst u
def ownWord (mean : Bool) (u : List Bool):=if mean then pairFst (pairSnd (pairSnd u)) else pairFst (pairSnd u)
def rank (u : List Bool):=pairSnd (pairSnd (pairSnd u))
def atomic (u : List Bool):=FormulaSignSlotRadialProviderProperRow.atomic (key u)
def query (mean : Bool) (u : List Bool):=pair (pair (key u) (ownWord mean u)) (rank u)

theorem key_FP : key∈FP:=pairFst_mem_FP
theorem ownWord_FP (mean : Bool) : ownWord mean∈FP:=by cases mean <;> polytime [ownWord]
theorem rank_FP : rank∈FP:=by polytime [rank]
theorem atomic_FP : atomic∈FP:=mem_FP_comp key_FP FormulaSignSlotRadialProviderProperRow.atomic_FP
theorem query_FP (mean : Bool) : query mean∈FP:=mem_FP_pair (mem_FP_pair key_FP (ownWord_FP mean)) rank_FP

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderProperRow.dimension FormulaSignSlotRadialProviderProperRow.initial

noncomputable def fieldMatch (mean : Bool) (u : List Bool):=FormulaSignSlotRadialProviderFieldEqualityList.packet
  (FormulaSignSlotRadialProviderAtomic.context (atomic u)) (FormulaSignSlotRadialProviderAtomic.word (atomic u))
  (FormulaSignSlotRadialProviderProperRow.context mean (key u)) (ownWord mean u)
  (IntegralMixedRoadmapBadProbePacket.matchTable (FormulaSignSlotRadialProviderAtomic.initial (atomic u))
    (IntegralMixedRoadmapProper.badPacket (atomic u)))

theorem fieldMatch_FP (mean : Bool) : fieldMatch mean∈FP:=by
  have HC:=mem_FP_comp (f:=atomic) (g:=FormulaSignSlotRadialProviderAtomic.context) atomic_FP FormulaSignSlotRadialProviderAtomic.context_FP
  have HW:=mem_FP_comp (f:=atomic) (g:=FormulaSignSlotRadialProviderAtomic.word) atomic_FP FormulaSignSlotRadialProviderAtomic.word_FP
  have HP:=mem_FP_comp key_FP (FormulaSignSlotRadialProviderProperRow.context_FP mean)
  have HT:=IntegralMixedRoadmapBadProbePacket.matchTable_FP
    ((FormulaSignSlotRadialProviderAtomic.initial_unary).comp atomic_FP)
    (mem_FP_comp atomic_FP IntegralMixedRoadmapProper.badPacket_FP)
  exact mem_FP_pair (mem_FP_pair HC HW) (mem_FP_pair (mem_FP_pair HP (ownWord_FP mean)) HT)

noncomputable def RowGood (z : List Bool):=
  IntegralMixedChronologicalCutCode.Good (FormulaSignSlotRadialProviderProperRow.dimension z)
    (FormulaSignSlotRadialProviderProperRow.creating z) (FormulaSignSlotRadialProviderProperRow.labels z)
    (FormulaSignSlotRadialProviderProperRow.offset z) (FormulaSignSlotRadialProviderProperRow.coordinate z) ∧
  IntegralMixedChronologicalMidpointCode.Good (FormulaSignSlotRadialProviderProperRow.dimension z)
    (FormulaSignSlotRadialProviderProperRow.creating z) (FormulaSignSlotRadialProviderProperRow.labels z)
    (FormulaSignSlotRadialProviderProperRow.oldProducer false z) (FormulaSignSlotRadialProviderProperRow.oldProducer true z)
    (FormulaSignSlotRadialProviderProperRow.offset z) (FormulaSignSlotRadialProviderProperRow.coordinate z)

theorem rowGood_FP : FPPred (RowGood):=
  (IntegralMixedChronologicalCutCode.good_FP (FormulaSignSlotRadialProviderProperRow.dimension_unary)
    (BinaryFn.ofUnary (FormulaSignSlotRadialProviderProperRow.creating_unary))
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderProperRow.offset_unary) FormulaSignSlotRadialProviderProperRow.coordinate_binary
    FormulaSignSlotRadialProviderProperRow.labels_FP).and
  (IntegralMixedChronologicalMidpointCode.good_FP (FormulaSignSlotRadialProviderProperRow.dimension_unary)
    (BinaryFn.ofUnary (FormulaSignSlotRadialProviderProperRow.creating_unary))
    (FormulaSignSlotRadialProviderProperRow.oldProducer_binary false) (FormulaSignSlotRadialProviderProperRow.oldProducer_binary true)
    (BinaryFn.ofUnary FormulaSignSlotRadialProviderProperRow.offset_unary) FormulaSignSlotRadialProviderProperRow.coordinate_binary
    FormulaSignSlotRadialProviderProperRow.labels_FP)

def SideGood (right : Bool) (z : List Bool):=IntegralMixedRoadmapChain.sideWord
  (FormulaSignSlotRadialProviderAtomic.payload (FormulaSignSlotRadialProviderProperRow.atomic z))
  (IntegralMixedRoadmapProper.levelIndex (FormulaSignSlotRadialProviderProperRow.atomic z))=if right then [true] else []
theorem sideGood_FP (right : Bool) : FPPred (SideGood right):=Brackets.stringEq_fppred
  (IntegralMixedRoadmapChain.sideWord_FP
    (mem_FP_comp (f:=FormulaSignSlotRadialProviderProperRow.atomic) (g:=FormulaSignSlotRadialProviderAtomic.payload)
      FormulaSignSlotRadialProviderProperRow.atomic_FP FormulaSignSlotRadialProviderAtomic.payload_FP)
    (IntegralMixedRoadmapProper.levelIndex_unary.comp FormulaSignSlotRadialProviderProperRow.atomic_FP))
  (constFn_mem_FP _)

noncomputable def language (right : Bool) : Language:={u |RowGood (key u)∧SideGood right (key u)∧
  query false u∈FormulaSignSlotRadialProviderProperRow.nearLanguage right∧
  query true u∈FormulaSignSlotRadialProviderProperRow.rankLanguage∧
  fieldMatch false u∈FormulaSignSlotRadialProviderFieldEqualityList.language∧
  fieldMatch true u∈FormulaSignSlotRadialProviderFieldEqualityList.language}

theorem decider (right : Bool) : SpaceDecider (language right):=by
  have EG:=SpaceFunction.ofFP _ (((rowGood_FP).and (sideGood_FP right)).comp key_FP).flag_mem_FP
  have EN:=((FormulaSignSlotRadialProviderProperRow.near_decider right).precompose _ (query_FP false)).flagEvaluator
  have ER:=((FormulaSignSlotRadialProviderProperRow.rank_decider).precompose _ (query_FP true)).flagEvaluator
  have EM (mode : Bool):=((FormulaSignSlotRadialProviderFieldEqualityList.decider).precompose _
    (fieldMatch_FP mode)).flagEvaluator
  apply (EG.andFlags (EN.andFlags (ER.andFlags ((EM false).andFlags (EM true))))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro u
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness

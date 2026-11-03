/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRankNative
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList

/-! # One coordinate certificate keeps two own-root full words

The ordinary word controls Near; the mean-centered word controls rank at
eta zero. Each is matched to ALL original older retained quotients.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (key ordinary mean rank : List Bool):=pair key (pair ordinary (pair mean rank))
def key (u : List Bool):=pairFst u
def ownWord (mean : Bool) (u : List Bool):=if mean then pairFst (pairSnd (pairSnd u)) else pairFst (pairSnd u)
def rank (u : List Bool):=pairSnd (pairSnd (pairSnd u))
def atomic (u : List Bool):=IntegralMixedRoadmapProperRow.atomic (key u)
def query (mean : Bool) (u : List Bool):=pair (pair (key u) (ownWord mean u)) (rank u)

theorem key_FP : key∈FP:=pairFst_mem_FP
theorem ownWord_FP (mean : Bool) : ownWord mean∈FP:=by cases mean <;> polytime [ownWord]
theorem rank_FP : rank∈FP:=by polytime [rank]
theorem atomic_FP : atomic∈FP:=mem_FP_comp key_FP IntegralMixedRoadmapProperRow.atomic_FP
theorem query_FP (mean : Bool) : query mean∈FP:=mem_FP_pair (mem_FP_pair key_FP (ownWord_FP mean)) rank_FP

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedRoadmapProperRow.dimension IntegralMixedRoadmapProperRow.initial

noncomputable def fieldMatch (mean : Bool) (u : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (IntegralMixedRoadmapAtomic.context (atomic u)) (IntegralMixedRoadmapAtomic.word (atomic u))
  (IntegralMixedRoadmapProperRow.context hn ht ha hR0 mean (key u)) (ownWord mean u)
  (IntegralMixedRoadmapBadProbePacket.matchTable (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (atomic u))
    (IntegralMixedRoadmapProper.badPacket (atomic u)))

theorem fieldMatch_FP (mean : Bool) : fieldMatch hn ht ha hR0 mean∈FP:=by
  have HC:=mem_FP_comp (f:=atomic) (g:=IntegralMixedRoadmapAtomic.context) atomic_FP IntegralMixedRoadmapAtomic.context_FP
  have HW:=mem_FP_comp (f:=atomic) (g:=IntegralMixedRoadmapAtomic.word) atomic_FP IntegralMixedRoadmapAtomic.word_FP
  have HP:=mem_FP_comp key_FP (IntegralMixedRoadmapProperRow.context_FP hn ht ha hR0 mean)
  have HT:=IntegralMixedRoadmapBadProbePacket.matchTable_FP
    ((IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0).comp atomic_FP)
    (mem_FP_comp atomic_FP IntegralMixedRoadmapProper.badPacket_FP)
  exact mem_FP_pair (mem_FP_pair HC HW) (mem_FP_pair (mem_FP_pair HP (ownWord_FP mean)) HT)

noncomputable def RowGood (z : List Bool):=
  IntegralMixedChronologicalCutCode.Good (IntegralMixedRoadmapProperRow.dimension hn ht ha hR0 z)
    (IntegralMixedRoadmapProperRow.creating hn ht ha hR0 z) (IntegralMixedRoadmapProperRow.labels z)
    (IntegralMixedRoadmapProperRow.offset z) (IntegralMixedRoadmapProperRow.coordinate z) ∧
  IntegralMixedChronologicalMidpointCode.Good (IntegralMixedRoadmapProperRow.dimension hn ht ha hR0 z)
    (IntegralMixedRoadmapProperRow.creating hn ht ha hR0 z) (IntegralMixedRoadmapProperRow.labels z)
    (IntegralMixedRoadmapProperRow.oldProducer false z) (IntegralMixedRoadmapProperRow.oldProducer true z)
    (IntegralMixedRoadmapProperRow.offset z) (IntegralMixedRoadmapProperRow.coordinate z)

theorem rowGood_FP : FPPred (RowGood hn ht ha hR0):=
  (IntegralMixedChronologicalCutCode.good_FP (IntegralMixedRoadmapProperRow.dimension_unary hn ht ha hR0)
    (BinaryFn.ofUnary (IntegralMixedRoadmapProperRow.creating_unary hn ht ha hR0))
    (BinaryFn.ofUnary IntegralMixedRoadmapProperRow.offset_unary) IntegralMixedRoadmapProperRow.coordinate_binary
    IntegralMixedRoadmapProperRow.labels_FP).and
  (IntegralMixedChronologicalMidpointCode.good_FP (IntegralMixedRoadmapProperRow.dimension_unary hn ht ha hR0)
    (BinaryFn.ofUnary (IntegralMixedRoadmapProperRow.creating_unary hn ht ha hR0))
    (IntegralMixedRoadmapProperRow.oldProducer_binary false) (IntegralMixedRoadmapProperRow.oldProducer_binary true)
    (BinaryFn.ofUnary IntegralMixedRoadmapProperRow.offset_unary) IntegralMixedRoadmapProperRow.coordinate_binary
    IntegralMixedRoadmapProperRow.labels_FP)

def SideGood (right : Bool) (z : List Bool):=IntegralMixedRoadmapChain.sideWord
  (IntegralMixedRoadmapAtomic.payload (IntegralMixedRoadmapProperRow.atomic z))
  (IntegralMixedRoadmapProper.levelIndex (IntegralMixedRoadmapProperRow.atomic z))=if right then [true] else []
theorem sideGood_FP (right : Bool) : FPPred (SideGood right):=Brackets.stringEq_fppred
  (IntegralMixedRoadmapChain.sideWord_FP
    (mem_FP_comp (f:=IntegralMixedRoadmapProperRow.atomic) (g:=IntegralMixedRoadmapAtomic.payload)
      IntegralMixedRoadmapProperRow.atomic_FP IntegralMixedRoadmapAtomic.payload_FP)
    (IntegralMixedRoadmapProper.levelIndex_unary.comp IntegralMixedRoadmapProperRow.atomic_FP))
  (constFn_mem_FP _)

noncomputable def language (right : Bool) : Language:={u |RowGood hn ht ha hR0 (key u)∧SideGood right (key u)∧
  query false u∈IntegralMixedRoadmapProperRow.nearLanguage hn ht ha hR0 right∧
  query true u∈IntegralMixedRoadmapProperRow.rankLanguage hn ht ha hR0∧
  fieldMatch hn ht ha hR0 false u∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)∧
  fieldMatch hn ht ha hR0 true u∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)}

theorem decider (right : Bool) : SpaceDecider (language hn ht ha hR0 right):=by
  have EG:=SpaceFunction.ofFP _ (((rowGood_FP hn ht ha hR0).and (sideGood_FP right)).comp key_FP).flag_mem_FP
  have EN:=((IntegralMixedRoadmapProperRow.near_decider hn ht ha hR0 right).precompose _ (query_FP false)).flagEvaluator
  have ER:=((IntegralMixedRoadmapProperRow.rank_decider hn ht ha hR0).precompose _ (query_FP true)).flagEvaluator
  have EM (mode : Bool):=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose _
    (fieldMatch_FP hn ht ha hR0 mode)).flagEvaluator
  apply (EG.andFlags (EN.andFlags (ER.andFlags ((EM false).andFlags (EM true))))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro u
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness

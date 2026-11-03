/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCriticalQuery
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # Native no-critical guard with independent prepared full and parent words

The prepared FULL word matches every older original quotient. A second
prepared PARENT word agrees with that full word through the existing joint
scan. The reserved child search is then the actual critical interval test.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCritical
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def atomic (z : List Bool):=pairFst (pairFst z)
def fullWord (z : List Bool):=pairSnd (pairFst z)
def parentWord (z : List Bool):=pairSnd z
theorem atomic_FP : atomic∈FP:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem fullWord_FP : fullWord∈FP:=mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem parentWord_FP : parentWord∈FP:=pairSnd_mem_FP

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.native

noncomputable def critical (z : List Bool):=query hn ht ha hR0 (pair (atomic z) (parentWord z))
noncomputable def joint (z : List Bool):=pair (critical hn ht ha hR0 z) (fullWord z)
noncomputable def fields (z : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (IntegralMixedRoadmapAtomic.context (atomic z)) (IntegralMixedRoadmapAtomic.word (atomic z))
  (context hn ht ha hR0 (atomic z)) (fullWord z)
  (IntegralMixedRoadmapBadProbePacket.matchTable (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 (atomic z))
    (IntegralMixedRoadmapProper.badPacket (atomic z)))

theorem critical_FP : critical hn ht ha hR0∈FP:=mem_FP_comp (mem_FP_pair atomic_FP parentWord_FP) (query_FP hn ht ha hR0)
theorem joint_FP : joint hn ht ha hR0∈FP:=mem_FP_pair (critical_FP hn ht ha hR0) fullWord_FP
theorem fields_FP : fields hn ht ha hR0∈FP:=by
  have HC:=mem_FP_comp (f:=atomic) (g:=IntegralMixedRoadmapAtomic.context) atomic_FP IntegralMixedRoadmapAtomic.context_FP
  have HW:=mem_FP_comp (f:=atomic) (g:=IntegralMixedRoadmapAtomic.word) atomic_FP IntegralMixedRoadmapAtomic.word_FP
  have HP:=mem_FP_comp atomic_FP (context_FP hn ht ha hR0)
  have HT:=IntegralMixedRoadmapBadProbePacket.matchTable_FP
    ((IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0).comp atomic_FP)
    (mem_FP_comp atomic_FP IntegralMixedRoadmapProper.badPacket_FP)
  exact mem_FP_pair (mem_FP_pair HC HW) (mem_FP_pair (mem_FP_pair HP fullWord_FP) HT)

noncomputable def Witness (z : List Bool):=IntegralMixedPhysicalCriticalInterval.Guard n false (critical hn ht ha hR0 z) ∧
  SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false)
    (critical hn ht ha hR0 z) (parentWord z) ∧
  SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false true)
    (critical hn ht ha hR0 z) (fullWord z) ∧
  fields hn ht ha hR0 z∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0) ∧
  IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha (radius_binary hR0) false (joint hn ht ha hR0 z) ∧
  critical hn ht ha hR0 z∉IntegralMixedPhysicalCriticalInterval.language hn ht ha (radius_binary hR0) false

theorem witness_evaluator : SpaceFunction (fun z=>[decide (Witness hn ht ha hR0 z)]):=by
  have EG:=SpaceFunction.ofFP _ ((IntegralMixedPhysicalCriticalInterval.guard_FP hn false).comp (critical_FP hn ht ha hR0)).flag_mem_FP
  have EP:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha (radius_binary hR0) false false)).precompose
    (fun z=>pair (critical hn ht ha hR0 z) (parentWord z)) (mem_FP_pair (critical_FP hn ht ha hR0) parentWord_FP)).flagEvaluator
  have EF:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha (radius_binary hR0) false true)).precompose
    (fun z=>joint hn ht ha hR0 z) (joint_FP hn ht ha hR0)).flagEvaluator
  have EM:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose _ (fields_FP hn ht ha hR0)).flagEvaluator
  have EA:=(IntegralMixedPhysicalCriticalBankEquality.scanEvaluator hn ht ha (radius_binary hR0) false).precompose _ (joint_FP hn ht ha hR0)
  have EN:=(((IntegralMixedPhysicalCriticalInterval.decider hn ht ha (radius_binary hR0) false).precompose _
    (critical_FP hn ht ha hR0)).flagEvaluator).postcompose _
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact (EG.andFlags (EP.andFlags (EF.andFlags (EM.andFlags (EA.andFlags EN))))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Witness,Function.comp_apply,joint,Set.mem_preimage,SquareSampleCompleteVertices.language,
      Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq,id_eq])

noncomputable def fullWidth (q : List Bool):=SquareSampleCompleteVertices.width
  (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false true) (canonical hn ht ha hR0 q)
noncomputable def parentWidth (q : List Bool):=SquareSampleCompleteVertices.width
  (IntegralMixedPhysicalCriticalPrefixes.input hn ht ha (radius_binary hR0) false false) (canonical hn ht ha hR0 q)
theorem fullWidth_unary : UnaryFn (fullWidth hn ht ha hR0):=
  (SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha (radius_binary hR0) false true)).comp
    (canonical_FP hn ht ha hR0)
theorem parentWidth_unary : UnaryFn (parentWidth hn ht ha hR0):=
  (SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalCriticalPrefixes.access hn ht ha (radius_binary hR0) false false)).comp
    (canonical_FP hn ht ha hR0)

noncomputable def NoCritical (q : List Bool):=∃wF : List Bool,wF.length=fullWidth hn ht ha hR0 q∧
  ∃wP : List Bool,wP.length=parentWidth hn ht ha hR0 q∧Witness hn ht ha hR0 (pair (pair q wF) wP)
theorem noCritical_evaluator : SpaceFunction (fun q=>[decide (NoCritical hn ht ha hR0 q)]):=by
  have E:=((witness_evaluator hn ht ha hR0).exists_words ((parentWidth_unary hn ht ha hR0).comp pairFst_mem_FP)).exists_words
    (fullWidth_unary hn ht ha hR0)
  exact E.congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [NoCritical,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.IntegralMixedRoadmapProperCritical

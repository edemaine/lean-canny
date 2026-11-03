/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNearNative
public import LeanCanny.Encoding.IntegralFramedZeroTarskiStatisticValue

/-! # Five actual zero-parameter statistics check a captured midpoint rank

The mean-centered source is queried at eta zero, with the captured MID
coordinate as epsilon-window center. The integer rank is the outer datum.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "A"=>IntegralMixedPhysicalMarkedPlan.native hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "hT"=>IntegralMixedPhysicalMarkedPlan.tables_native hn ht ha (radius_binary hR0) false
local notation "hr"=>IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false
local notation "hf"=>IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha (radius_binary hR0) false
local notation "hd"=>IntegralMixedPhysicalTraceCutTest.fallback hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedPhysicalMarkedPlan.native
  IntegralMixedPhysicalMarkedPlan.tables IntegralMixedFramedHistoryFamilyBits.family
  parent terminal pointIndex IntegralFramedZeroTarskiStatistic.value

noncomputable def zeroStatistic (power : Fin 3) (negative : Bool):=IntegralFramedZeroTarskiStatistic.value
  (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
  (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
  (positive hn ht ha hR0 true) hf hd power negative

theorem zeroStatistic_evaluator (power : Fin 3) (negative : Bool) :
    SpaceFunction (fun u=>SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 power negative u)):=
  IntegralFramedZeroTarskiStatistic.evaluator (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
    (positive hn ht ha hR0 true) (A).parameters (A).nodes (A).factor (A).seed (metadata hn ht ha hR0)
    (IntegralMixedPhysicalTraceCutTest.probeControls hn ht ha (radius_binary hR0) false)
    (IntegralMixedPhysicalTraceCutTest.probeBounds hn ht ha (radius_binary hR0) false)
    (A).liftedData (A).controls (A).bounds T hT hr
    (parent_FP hn ht ha hR0 true) (terminal_FP hn ht ha hR0 true) (pointIndex_binary hn ht ha hR0 true true)
    (sampler_access hn ht ha hR0 true) hf hd power negative

noncomputable def rankPacket (u : List Bool):=OrderedWindowStatisticBits.pack (pairSnd u)
  (SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 0 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 2 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 1 false (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 2 true (IntegralFramedPhysicalNear.reset u)))
  (SignStatisticBits.integerCode (zeroStatistic hn ht ha hR0 1 true (IntegralFramedPhysicalNear.reset u)))

theorem rankPacket_evaluator : SpaceFunction (rankPacket hn ht ha hR0):=by
  have E (p : Fin 3) (negative : Bool):=(zeroStatistic_evaluator hn ht ha hR0 p negative).precompose
    IntegralFramedPhysicalNear.reset IntegralFramedPhysicalNear.reset_FP
  exact (SpaceFunction.ofFP pairSnd pairSnd_mem_FP).pairOutputs ((E 0 false).pairOutputs
    ((E 2 false).pairOutputs ((E 1 false).pairOutputs ((E 2 true).pairOutputs (E 1 true)))))

noncomputable def RankAccept (u : List Bool):=OrderedWindowStatisticBits.Accept (rankPacket hn ht ha hR0 u)
noncomputable def rankLanguage : Language:={u |
  IntegralFramedPhysicalNear.Metadata (B).parameters (B).plan (B).data (parent hn ht ha hR0 true)
    (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true) (pointIndex hn ht ha hR0 true true) (pairFst (pairFst u)) ∧
  SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds (terminal hn ht ha hR0 true) (positive hn ht ha hR0 true))
      (pairFst (pairFst u)) (pairSnd (pairFst u)) ∧ RankAccept hn ht ha hR0 u}

theorem rank_decider : SpaceDecider (rankLanguage hn ht ha hR0):=by
  have HM:=SpaceFunction.ofFP _ ((IntegralFramedPhysicalNear.metadata_FP (B).parameters (B).plan (B).data
    (parent hn ht ha hR0 true) (terminal hn ht ha hR0 true) (pointIndex hn ht ha hR0 true true)
    (pointIndex hn ht ha hR0 true true) (A).parameters (parent_FP hn ht ha hR0 true) (terminal_FP hn ht ha hR0 true)
    (pointIndex_binary hn ht ha hR0 true true) (pointIndex_binary hn ht ha hR0 true true)).comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).flag_mem_FP
  have HV:=((SquareSampleCompleteVertices.decider (sampler_access hn ht ha hR0 true)).flagEvaluator).precompose pairFst pairFst_mem_FP
  have HR:=(rankPacket_evaluator hn ht ha hR0).postcompose
    (fun q=>[decide (OrderedWindowStatisticBits.Accept q)]) OrderedWindowStatisticBits.accept_fppred.flag_mem_FP
  apply (HM.andFlags (HV.andFlags HR)).decider (fun q=>decide (q=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro u
  simp only [Function.comp_apply,RankAccept,rankLanguage,SquareSampleCompleteVertices.language,
    Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

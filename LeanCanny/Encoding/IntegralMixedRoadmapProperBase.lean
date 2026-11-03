/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSearch
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralMixedPhysicalCutOrderedInterval
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext

/-! # Original-only midpoint, order and ordinary-bad guards

These are components of a proper incidence certificate. They do not yet
include the actual critical-value or coordinate Near tests.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false

noncomputable def fullCount (q : List Bool):=IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0)
  (IntegralMixedRoadmapAtomic.context q)
theorem fullCount_unary : UnaryFn (fullCount hn ht ha hR0):=
  (IntegralMixedPhysicalFieldEquality.count_unary hn ht ha (radius_binary hR0)).comp IntegralMixedRoadmapAtomic.context_FP
noncomputable def endpointIndex (right : Bool) (q : List Bool):=fullCount hn ht ha hR0 q-1-producer right q
theorem endpointIndex_binary (right : Bool) : BinaryFn (endpointIndex hn ht ha hR0 right):=
  ((BinaryFn.ofUnary (fullCount_unary hn ht ha hR0)).sub (BinaryFn.const 1)).sub (producer_binary right)
noncomputable def orderContext (q : List Bool):=pair (IntegralMixedRoadmapAtomic.root q)
  (pair [] (pair (BinaryNatCode.encode (endpointIndex hn ht ha hR0 false q))
    (BinaryNatCode.encode (endpointIndex hn ht ha hR0 true q))))
noncomputable def orderQuery (q : List Bool):=pair (orderContext hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.word q)
theorem orderContext_FP : orderContext hn ht ha hR0∈FP:=mem_FP_pair IntegralMixedRoadmapAtomic.root_FP
  (mem_FP_pair (constFn_mem_FP []) (mem_FP_pair
    (endpointIndex_binary hn ht ha hR0 false).bits_mem_FP (endpointIndex_binary hn ht ha hR0 true).bits_mem_FP))
theorem orderQuery_FP : orderQuery hn ht ha hR0∈FP:=
  mem_FP_pair (orderContext_FP hn ht ha hR0) IntegralMixedRoadmapAtomic.word_FP
noncomputable def order :=IntegralMixedPhysicalCutOrderedInterval.order hn ht ha (radius_binary hR0) false∘orderQuery hn ht ha hR0

theorem order_evaluator : SpaceFunction (order hn ht ha hR0):=
  (IntegralMixedPhysicalCutOrderedInterval.order_evaluator hn ht ha (radius_binary hR0) false).precompose
    (orderQuery hn ht ha hR0) (orderQuery_FP hn ht ha hR0)

noncomputable def NoBad (q : List Bool):=IntegralMixedRoadmapBadProbeSearch.NoBadProbe hn ht ha
  (radius_binary hR0) (badPacket q)
theorem noBad_evaluator : SpaceFunction (fun q=>[decide (NoBad hn ht ha hR0 q)]):=
  (IntegralMixedRoadmapBadProbeSearch.noBadProbe_evaluator hn ht ha (radius_binary hR0)).precompose badPacket badPacket_FP
noncomputable def Midpoint (q : List Bool):=midCompanions (D q) (I q) q∈
  IntegralMixedPhysicalPointCompanionScan.language hn ht ha (radius_binary hR0) false

theorem midpoint_decider : SpaceDecider {q |Midpoint hn ht ha hR0 q}:=
  (IntegralMixedPhysicalPointCompanionScan.decider hn ht ha (radius_binary hR0) false).precompose
    (fun q=>midCompanions (D q) (I q) q)
    (midCompanions_FP (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0) (IntegralMixedRoadmapAtomic.initial_unary hn ht ha hR0))

noncomputable def OrderBounds (q : List Bool):=producer false q<fullCount hn ht ha hR0 q∧producer true q<fullCount hn ht ha hR0 q
theorem orderBounds_FP : FPPred (OrderBounds hn ht ha hR0):=
  ((producer_binary false).lt (BinaryFn.ofUnary (fullCount_unary hn ht ha hR0))).and
    ((producer_binary true).lt (BinaryFn.ofUnary (fullCount_unary hn ht ha hR0)))

noncomputable def Base (q : List Bool):=0<IntegralMixedRoadmapAtomic.depth q∧OrderBounds hn ht ha hR0 q∧
  Midpoint hn ht ha hR0 q∧NoBad hn ht ha hR0 q∧order hn ht ha hR0 q=InfinitesimalSign.encode 1
noncomputable def baseLanguage : Language:={q |Base hn ht ha hR0 q}

theorem base_decider : SpaceDecider (baseLanguage hn ht ha hR0):=by
  have EP:=SpaceFunction.ofFP _ (((BinaryFn.const 0).lt (BinaryFn.ofUnary IntegralMixedRoadmapAtomic.depth_unary)).and
    (orderBounds_FP hn ht ha hR0)).flag_mem_FP
  have EM:=(midpoint_decider hn ht ha hR0).flagEvaluator
  have EB:=noBad_evaluator hn ht ha hR0
  have EO:=(order_evaluator hn ht ha hR0).postcompose (fun v=>[decide (v=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (EP.andFlags (EM.andFlags (EB.andFlags EO))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Function.comp_apply,Base,baseLanguage,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc]

end LeanCanny.Encoding.IntegralMixedRoadmapProper

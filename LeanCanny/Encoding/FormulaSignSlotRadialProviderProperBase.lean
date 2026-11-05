/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperLayout
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeSearch
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicCompanions
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEquality
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval

/-! # Original-only midpoint, order and ordinary-bad guards

These are components of a proper incidence certificate. They do not yet
include the actual critical-value or coordinate Near tests.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "I"=>FormulaSignSlotRadialProviderAtomic.initial
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input

noncomputable def fullCount (q : List Bool):=FormulaSignSlotRadialProviderFieldEquality.count
  (FormulaSignSlotRadialProviderAtomic.context q)
theorem fullCount_unary : UnaryFn (fullCount):=
  (FormulaSignSlotRadialProviderFieldEquality.count_unary).comp FormulaSignSlotRadialProviderAtomic.context_FP
noncomputable def endpointIndex (right : Bool) (q : List Bool):=fullCount q-1-producer right q
theorem endpointIndex_binary (right : Bool) : BinaryFn (endpointIndex right):=
  ((BinaryFn.ofUnary (fullCount_unary)).sub (BinaryFn.const 1)).sub (producer_binary right)
noncomputable def orderContext (q : List Bool):=pair (FormulaSignSlotRadialProviderAtomic.root q)
  (pair [] (pair (BinaryNatCode.encode (endpointIndex false q))
    (BinaryNatCode.encode (endpointIndex true q))))
noncomputable def orderQuery (q : List Bool):=pair (orderContext q) (FormulaSignSlotRadialProviderAtomic.word q)
theorem orderContext_FP : orderContext∈FP:=mem_FP_pair FormulaSignSlotRadialProviderAtomic.root_FP
  (mem_FP_pair (constFn_mem_FP []) (mem_FP_pair
    (endpointIndex_binary false).bits_mem_FP (endpointIndex_binary true).bits_mem_FP))
theorem orderQuery_FP : orderQuery∈FP:=
  mem_FP_pair (orderContext_FP) FormulaSignSlotRadialProviderAtomic.word_FP
noncomputable def order :=FormulaSignSlotRadialProviderCutInterval.order∘orderQuery

theorem order_evaluator : SpaceFunction (order):=
  (FormulaSignSlotRadialProviderCutInterval.order_evaluator).precompose
    (orderQuery) (orderQuery_FP)

noncomputable def NoBad (q : List Bool):=FormulaSignSlotRadialProviderBadProbeSearch.NoBadProbe (badPacket q)
theorem noBad_evaluator : SpaceFunction (fun q=>[decide (NoBad q)]):=
  (FormulaSignSlotRadialProviderBadProbeSearch.noBadProbe_evaluator).precompose badPacket badPacket_FP
noncomputable def Midpoint (q : List Bool):=midCompanions (D q) (I q) q∈
  FormulaSignSlotRadialProviderAtomic.Companions.language

theorem midpoint_decider : SpaceDecider {q |Midpoint q}:=
  (FormulaSignSlotRadialProviderAtomic.Companions.decider).precompose
    (fun q=>midCompanions (D q) (I q) q)
    (midCompanions_FP (FormulaSignSlotRadialProviderAtomic.dimension_unary) (FormulaSignSlotRadialProviderAtomic.initial_unary))

noncomputable def OrderBounds (q : List Bool):=producer false q<fullCount q∧producer true q<fullCount q
theorem orderBounds_FP : FPPred (OrderBounds):=
  ((producer_binary false).lt (BinaryFn.ofUnary (fullCount_unary))).and
    ((producer_binary true).lt (BinaryFn.ofUnary (fullCount_unary)))

noncomputable def Base (q : List Bool):=0<FormulaSignSlotRadialProviderAtomic.depth q∧OrderBounds q∧
  Midpoint q∧NoBad q∧order q=InfinitesimalSign.encode 1
noncomputable def baseLanguage : Language:={q |Base q}

theorem base_decider : SpaceDecider (baseLanguage):=by
  have EP:=SpaceFunction.ofFP _ (((BinaryFn.const 0).lt (BinaryFn.ofUnary FormulaSignSlotRadialProviderAtomic.depth_unary)).and
    (orderBounds_FP)).flag_mem_FP
  have EM:=(midpoint_decider).flagEvaluator
  have EB:=noBad_evaluator
  have EO:=(order_evaluator).postcompose (fun v=>[decide (v=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (EP.andFlags (EM.andFlags (EB.andFlags EO))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [Function.comp_apply,Base,baseLanguage,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq,and_assoc]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper

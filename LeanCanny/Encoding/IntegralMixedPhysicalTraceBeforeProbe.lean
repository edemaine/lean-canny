/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
/-! # The reserved last probe is excluded from meaningful cut-root validation

Every EARLIER creating cut keeps its original full head/root guard, on one
fixed full context and word. The final creating instruction is deliberately
not scanned. The caller must identify it as the reserved interval probe.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralMixedPhysicalTraceCutScan (count count_unary StageCut stageCut_FP)
open IntegralMixedPhysicalTraceCutGuards (Guards)
open IntegralFramedTraceCutScan (stagePacket stageQuery stageQuery_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable def holds (q : List Bool):=∀j<count hn ht ha hR outer q-1,
 StageCut hn ht ha hR outer (stagePacket q j)→Guards hn ht ha hR outer (stagePacket q j)

theorem earlier_iff (q : List Bool) : holds hn ht ha hR outer q ↔
    ∀j<count hn ht ha hR outer q,j+1<count hn ht ha hR outer q→
      StageCut hn ht ha hR outer (stagePacket q j)→Guards hn ht ha hR outer (stagePacket q j):=by
 constructor
 · intro H j _ hj
   exact H j (by omega)
 · intro H j hj
   exact H j (by omega) (by omega)

theorem except_last_iff (q : List Bool) : holds hn ht ha hR outer q ↔
    ∀j<count hn ht ha hR outer q,j≠count hn ht ha hR outer q-1→
      StageCut hn ht ha hR outer (stagePacket q j)→Guards hn ht ha hR outer (stagePacket q j):=by
 constructor
 · intro H j hj hlast
   exact H j (by omega)
 · intro H j hj
   exact H j (by omega) (by omega)

theorem bound_actual (ctx w : List Bool) : count hn ht ha hR outer (pair ctx w)-1=
    IntegralFramedTraceCutMetadata.length (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).parameters
      (IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR outer).plan ctx-1:=
 congrArg (fun m : ℕ=>m-1) (IntegralMixedPhysicalTraceCutScan.count_eq_length hn ht ha hR outer ctx w)

theorem evaluator : SpaceFunction (fun q=>[decide (holds hn ht ha hR outer q)]):=by
 have EG:=IntegralMixedPhysicalTraceCutGuards.evaluator hn ht ha hR outer
   (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)
 have E:=SpaceFunction.branch (fun b=>decide (StageCut hn ht ha hR outer b))
   (stageCut_FP hn ht ha hR outer).flag_mem_FP EG (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
 have EI : SpaceFunction (fun b=>[decide (StageCut hn ht ha hR outer b→Guards hn ht ha hR outer b)]):=
   E.congr (by
     funext b
     by_cases HB:StageCut hn ht ha hR outer b <;>
       simp only [HB,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,
         true_implies,false_implies,decide_true])
 have EU:=(EI.precompose stageQuery stageQuery_FP).forall_unary
   ((count_unary hn ht ha hR outer).sub (UnaryFn.const 1))
 exact EU.congr (by
   funext q
   apply congrArg List.singleton
   apply Bool.eq_iff_iff.mpr
   simp only [holds,Function.comp_apply,stageQuery,stagePacket,pairFst_pair,pairSnd_pair,
     List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language:={q |
 SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext (pairFst q)) (pairSnd q) ∧
 holds hn ht ha hR outer q}

theorem decider : SpaceDecider (language hn ht ha hR outer):=by
 have EV:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)).precompose
   IntegralMixedPhysicalMarkedTest.leafQuery IntegralMixedPhysicalMarkedTest.leafQuery_FP).flagEvaluator
 have EU:=evaluator hn ht ha hR outer
 apply (EV.andFlags EU).decider (fun v=>decide (v=[true]))
   (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
 intro q
 simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
   IntegralMixedPhysicalMarkedTest.leafQuery,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedPhysicalTraceBeforeProbe

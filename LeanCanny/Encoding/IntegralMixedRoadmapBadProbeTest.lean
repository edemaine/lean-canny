/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientIntervalComplete
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native correlated witnesses to failure of a reserved interval probe

The base full word and a freshly sampled prepared-root word agree on every
old scalar producer. The last producer belongs only to the new probe. The
factor guard checks validity and the exact specialized degree. Geometric
identification with the whole ordinary bad set is a separate theorem.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "A" => IntegralFramedBankQuery.Access.parameters (IntegralMixedPhysicalMarkedPlan.native hn ht ha hR false)
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

noncomputable def dimension (q : List Bool):=(P).ambient (IntegralMixedRoadmapBadProbePacket.root (pairFst q))
noncomputable def initial (q : List Bool):=dimension hn ht ha hR q+5
noncomputable def width (q : List Bool):=(P).width (IntegralMixedRoadmapBadProbePacket.root (pairFst q))
theorem dimension_unary : UnaryFn (dimension hn ht ha hR):=
  (A).ambient.comp (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.root_FP)
theorem initial_unary : UnaryFn (initial hn ht ha hR):=(dimension_unary hn ht ha hR).add (UnaryFn.const 5)
theorem width_unary : UnaryFn (width hn ht ha hR):=
  (A).width.comp (mem_FP_comp pairFst_mem_FP IntegralMixedRoadmapBadProbePacket.root_FP)

noncomputable def intervalContext (q : List Bool):=
  IntegralMixedRoadmapBadProbePacket.intervalContext (dimension hn ht ha hR q) (initial hn ht ha hR q) q
noncomputable def intervalPacket (z : List Bool):=pair (intervalContext hn ht ha hR (pairFst z)) (pairSnd z)
noncomputable def fieldPacket (z : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (pair (IntegralMixedRoadmapBadProbePacket.root (pairFst (pairFst z))) []) (IntegralMixedRoadmapBadProbePacket.word (pairFst (pairFst z)))
  (pair (IntegralMixedRoadmapBadProbePacket.preparedRoot (dimension hn ht ha hR (pairFst z)) (pairFst z)) []) (pairSnd z)
  (IntegralMixedRoadmapBadProbePacket.matchTable (initial hn ht ha hR (pairFst z)) (pairFst (pairFst z)))

theorem intervalContext_FP : intervalContext hn ht ha hR∈FP:=
  IntegralMixedRoadmapBadProbePacket.intervalContext_FP (dimension_unary hn ht ha hR) (initial_unary hn ht ha hR)
theorem intervalPacket_FP : intervalPacket hn ht ha hR∈FP:=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (intervalContext_FP hn ht ha hR)) pairSnd_mem_FP

theorem fieldPacket_FP : fieldPacket hn ht ha hR∈FP:=by
  have HQ:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HC:=mem_FP_pair (mem_FP_comp HQ IntegralMixedRoadmapBadProbePacket.root_FP) (constFn_mem_FP [])
  have HR:=mem_FP_comp pairFst_mem_FP
    (IntegralMixedRoadmapBadProbePacket.preparedRoot_FP (dimension_unary hn ht ha hR))
  exact mem_FP_pair (mem_FP_pair HC (mem_FP_comp (g:=IntegralMixedRoadmapBadProbePacket.word) HQ IntegralMixedRoadmapBadProbePacket.word_FP))
    (mem_FP_pair (mem_FP_pair (mem_FP_pair HR (constFn_mem_FP [])) pairSnd_mem_FP)
      (IntegralMixedRoadmapBadProbePacket.matchTable_FP ((initial_unary hn ht ha hR).comp pairFst_mem_FP) HQ))

noncomputable def Witness (z : List Bool) : Prop:=
  IntegralMixedRoadmapBadProbePacket.HintGood (dimension hn ht ha hR (pairFst z)) (initial hn ht ha hR (pairFst z))
    (width hn ht ha hR (pairFst z)) (pairFst z) ∧
  fieldPacket hn ht ha hR z∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR ∧
  SquareSampleCompleteVertices.Valid S (intervalContext hn ht ha hR (pairFst z)) (pairSnd z) ∧
  IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha hR false (intervalPacket hn ht ha hR z) ∧
  IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR false (intervalPacket hn ht ha hR z) ∧
  intervalPacket hn ht ha hR z∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR false

noncomputable def language : Language:={z | Witness hn ht ha hR z}

theorem evaluator : SpaceFunction (fun z=>[decide (Witness hn ht ha hR z)]):=by
  have EH:=SpaceFunction.ofFP _ ((IntegralMixedRoadmapBadProbePacket.hintGood_FP
    (dimension_unary hn ht ha hR) (initial_unary hn ht ha hR) (width_unary hn ht ha hR)).comp
      pairFst_mem_FP).flag_mem_FP
  have EF:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha hR).precompose _ (fieldPacket_FP hn ht ha hR)).flagEvaluator
  have EV:=((SquareSampleCompleteVertices.decider
    (IntegralMixedPhysicalMarkedNative.access hn ht ha hR false)).precompose _
      (intervalPacket_FP hn ht ha hR)).flagEvaluator
  have EB:=SpaceFunction.ofFP _ (((IntegralMixedPhysicalCutOpenInterval.bounds_FP hn ht ha hR false).comp
    (intervalPacket_FP hn ht ha hR))).flag_mem_FP
  have EG:=(IntegralMixedPhysicalCutCoefficientOnly.evaluator hn ht ha hR false).precompose _
    (intervalPacket_FP hn ht ha hR)
  have EN:=(((IntegralMixedPhysicalCutCoefficientInterval.decider hn ht ha hR false).precompose _ (intervalPacket_FP hn ht ha hR)).flagEvaluator).postcompose _
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact (EH.andFlags (EF.andFlags (EV.andFlags (EB.andFlags (EG.andFlags EN))))).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,id_eq,pairFst_pair,pairSnd_pair,Witness,Set.mem_preimage,SquareSampleCompleteVertices.language,intervalPacket,
      Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language hn ht ha hR):=by
  apply (evaluator hn ht ha hR).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,List.cons.injEq,and_true,Set.mem_ofPred_eq,decide_eq_true_eq]
theorem mem_PSPACE : language hn ht ha hR∈PSPACE:=(decider hn ht ha hR).mem_PSPACE

noncomputable def probeWordWidth (q : List Bool):=SquareSampleCompleteVertices.width S (intervalContext hn ht ha hR q)
theorem probeWordWidth_unary : UnaryFn (probeWordWidth hn ht ha hR):=
  (SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalMarkedNative.access hn ht ha hR false)).comp
    (intervalContext_FP hn ht ha hR)
noncomputable def HasWitness (q : List Bool):=∃w : List Bool,
  w.length=probeWordWidth hn ht ha hR q ∧ Witness hn ht ha hR (pair q w)
theorem witness_word_length (q w : List Bool) (h : Witness hn ht ha hR (pair q w)) :
    w.length=probeWordWidth hn ht ha hR q :=by
  have HV : SquareSampleCompleteVertices.Valid S (intervalContext hn ht ha hR q) w:=by
    simpa only [pairFst_pair,pairSnd_pair] using h.2.2.1
  exact (Classical.choose HV).1

theorem hasWitness_iff (q : List Bool) :
    HasWitness hn ht ha hR q ↔ ∃w : List Bool,Witness hn ht ha hR (pair q w) :=by
  constructor
  · rintro ⟨w,_,h⟩
    exact ⟨w,h⟩
  · rintro ⟨w,h⟩
    exact ⟨w,witness_word_length hn ht ha hR q w h,h⟩

theorem hasWitness_evaluator : SpaceFunction (fun q=>[decide (HasWitness hn ht ha hR q)]):=by
  exact ((evaluator hn ht ha hR).exists_words (probeWordWidth_unary hn ht ha hR)).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [HasWitness,List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTest

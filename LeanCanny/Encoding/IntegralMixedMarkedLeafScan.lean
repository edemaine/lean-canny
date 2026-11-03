/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedLeafTest
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Native validity of every original prelude polynomial at the same vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedLeafScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedCandidateReplayNew (input sampleContext)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

def probe (z : List Bool) := pair (pair (sampleContext (pairFst (pairFst z))) (pairSnd (pairFst z)))
  (IntegralMixedCandidateReplayDatum.packet [] (pairSnd z).length 0)
theorem probe_FP : probe∈FP := by
  have HH : (fun z=>pairFst z)∈FP:=pairFst_mem_FP
  have HQ : (fun z=>pairFst (pairFst z))∈FP:=mem_FP_comp (f:=pairFst) (g:=pairFst) HH HH
  have HI : BinaryFn (fun z : List Bool=>(pairSnd z).length):=BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)
  exact mem_FP_pair (mem_FP_pair (mem_FP_comp HQ IntegralMixedCandidateReplayNew.sampleContext_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) (mem_FP_pair (constFn_mem_FP [])
      (mem_FP_pair HI.bits_mem_FP (constFn_mem_FP (BinaryNatCode.encode 0))))

noncomputable def holds (q : List Bool) : Prop := ∀ i<number n (pairFst q)+8,
  IntegralMixedMarkedLeafTest.value hn ht ha hR (probe (pair q (List.replicate i true)))=InfinitesimalSign.encode 0

attribute [local irreducible] IntegralMixedMarkedLeafTest.value

theorem holds_evaluator : SpaceFunction (fun q=>[decide (holds hn ht ha hR q)]) := by
  have E:=((IntegralMixedMarkedLeafTest.evaluator hn ht ha hR).precompose probe probe_FP).postcompose
    (fun z=>[decide (z=InfinitesimalSign.encode 0)]) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have HN : UnaryFn (fun q=>number n (pairFst q)+8):=((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).comp pairFst_mem_FP).add (UnaryFn.const 8)
  exact (E.forall_unary HN).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language := {q |
  SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext (pairFst q)) (pairSnd q) ∧ holds hn ht ha hR q}

theorem decider : SpaceDecider (language hn ht ha hR) := by
  have E:=((SquareSampleCompleteVertices.decider (IntegralFramedBankQuery.input_access
    (IntegralMixedAuxiliaryMarkedIntegerPlan.bank hn ht ha hR) (IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR))).precompose
    (fun q=>pair (sampleContext (pairFst q)) (pairSnd q))
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP IntegralMixedCandidateReplayNew.sampleContext_FP) pairSnd_mem_FP)).flagEvaluator
  apply (E.andFlags (holds_evaluator hn ht ha hR)).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

theorem holds_iff (ctx w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext ctx) w) :
    holds hn ht ha hR (pair ctx w) ↔ ∀ i<number n ctx+8,
      ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial (pair ctx (BinaryNatCode.encode i))).eval₂
        (Int.castRingHom ℝ) (IntegralMixedMarkedLeafTest.point hn ht ha hR ctx w hv i)=0 := by
  have HP (i : ℕ):=IntegralMixedMarkedLeafTest.packet hn ht ha hR ctx w hv i
  simp only [holds,pairFst_pair,probe,pairSnd_pair,List.length_replicate]
  simp_rw [HP,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]

theorem accepted_roots (q : List Bool) (hq : q∈language hn ht ha hR) :
    ∃ hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR) (sampleContext (pairFst q)) (pairSnd q),
      ∀ i<number n (pairFst q)+8,
        ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).polynomial (pair (pairFst q) (BinaryNatCode.encode i))).eval₂
          (Int.castRingHom ℝ) (IntegralMixedMarkedLeafTest.point hn ht ha hR (pairFst q) (pairSnd q) hv i)=0 := by
  obtain ⟨hv,HG⟩:=hq
  refine ⟨hv,?_⟩
  apply (holds_iff hn ht ha hR (pairFst q) (pairSnd q) hv).mp
  simpa only [holds,probe,pairFst_pair,pairSnd_pair] using HG

end LeanCanny.Encoding.IntegralMixedMarkedLeafScan

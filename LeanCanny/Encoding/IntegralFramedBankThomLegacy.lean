/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankQueryLegacy
public import LeanCanny.Encoding.IntegralFramedBankThomEquality

/-! # Native equality from an original candidate to a current-Q replay

The original side performs its own planning and modulus pullback. The replay
side uses its native current-Q controls. Both evaluate the same implicit
integer derivatives at their own actual complete bank coordinates.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankThomLegacy
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralFramedBankThomEquality (context word probe probe_FP agrees language)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (A B : Bank) (a : IntegralCriticalHistoryTask.Access A.parameters)
  (s : IntegralMixedFramedNativeBits.Syntax A.parameters A.plan A.data)
  (hs : IntegralMixedFramedStepHeight.FamilyInputs A.parameters A.plan s.nodes s.factor s.seed)
  (hF : ∀ root,1≤s.factor root) (hL : ∀ root,1≤s.nodes root)
  (hLB : BinaryFn A.nodes) (hFB : BinaryFn A.factor) (hCB : BinaryFn A.seed)
  (hk : A.key∈FP) (hi : UnaryFn (fun c=>(A.coordinate c).val)) (hB : IntegralFramedBankQuery.Access B)
  (Q : IntegerPolynomialRootQueriesBits.Source) (hQ : IntegerPolynomialRootQueriesBits.Access Q)

include a s hs hF hL hLB hFB hCB hk hi hB hQ

theorem scanEvaluator : SpaceFunction (fun q=>[decide (agrees A B Q q)]) := by
  have D:=IntegerPolynomialIteratedDerivativeBits.access hQ
  have L:=(IntegralFramedBankQueryLegacy.evaluator A a s hs hF hL hLB hFB hCB hk hi _ D).precompose
    (probe false) (probe_FP false)
  have R:=(IntegralFramedBankQuery.evaluator B hB _ D).precompose (probe true) (probe_FP true)
  have E:=(L.pairOutputs R).postcompose (fun z=>[decide (pairFst z=pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  have ND : BinaryFn (fun q=>Q.degree (context q)):=hQ.degree.comp pairFst_mem_FP
  exact (E.forall_binary (ND.add (BinaryFn.const 1))).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [agrees,Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language A B Q) := by
  have HA : (fun q=>pair (context q) (word false q))∈FP := by polytime [context,word]
  have HB : (fun q=>pair (context q) (word true q))∈FP := by polytime [context,word]
  have L:=((SquareSampleCompleteVertices.decider
    (IntegralFramedBankQueryLegacy.input_access A a s hs hF hL hLB hFB hCB hk)).precompose _ HA).flagEvaluator
  have R:=((SquareSampleCompleteVertices.decider (IntegralFramedBankQuery.input_access B hB)).precompose _ HB).flagEvaluator
  apply (L.andFlags (R.andFlags (scanEvaluator A B a s hs hF hL hLB hFB hCB hk hi hB Q hQ))).decider
    (fun z=>decide (z=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,SquareSampleCompleteVertices.language,
    pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language A B Q∈PSPACE := (decider A B a s hs hF hL hLB hFB hCB hk hi hB Q hQ).mem_PSPACE

end LeanCanny.Encoding.IntegralFramedBankThomLegacy

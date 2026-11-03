/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedLeafScan
public import LeanCanny.Encoding.IntegralFramedBankTermCurrentQ
public import LeanCanny.ETR.BoundedMarkedParameterTerm
/-! # Original-only native tests of marked replay equations

The large power leaves are variables. The only expanded power degree is a
unary linear function of original term size; no radius power is serialized.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPointTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedCandidateReplayNew (bank input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀ q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)

def charge (t : List Bool→Term) (ctx : List Bool) := (t (original ctx)).toData.size
def degree (t : List Bool→Term) (ctx : List Bool) := LeanCanny.Geometry.BoundedZeroSource.powerDegree (charge t ctx)
def markWord (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :=
  (BoundedMarkedParameterTerm.mark (t (original ctx)) (number n ctx)).toData.toBits
def regularWord (n : List Bool→ℕ) (t : List Bool→Term) (ctx : List Bool) :=
  (BoundedMarkedParameterTerm.regular (t (original ctx)) (number n ctx) (degree t ctx)).toData.toBits

theorem original_FP : original∈FP:=mem_FP_comp (f:=pairFst) (g:=pairFst) pairFst_mem_FP pairFst_mem_FP
include ht in
theorem charge_unary : UnaryFn (charge t) :=
  (LeanCanny.Geometry.AuxiliaryCandidateRegularLift.allowance_unary ht).comp original_FP
include ht in
theorem degree_unary : UnaryFn (degree t) :=
  (UnaryFn.const 2).mul (((UnaryFn.const 2).mul ((UnaryFn.const 2).mul ((charge_unary ht).add (UnaryFn.const 2)))).add (UnaryFn.const 1))

include hn ht in
theorem markWord_FP : markWord n t∈FP :=
  BoundedMarkedParameterTerm.mark_FP (mem_FP_comp original_FP ht) (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
include hn ht in
theorem regularWord_FP : regularWord n t∈FP :=
  BoundedMarkedParameterTerm.regular_FP (mem_FP_comp original_FP ht) (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn) (degree_unary ht)

def probe (q : List Bool) := pair (pair (sampleContext (pairFst q)) (pairSnd q)) []
theorem probe_FP : probe∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp pairFst_mem_FP IntegralMixedCandidateReplayNew.sampleContext_FP) pairSnd_mem_FP) (constFn_mem_FP [])

noncomputable def markValue : List Bool→List Bool := IntegralFramedBankTermCurrentQ.value (bank hn ht ha hR) (markWord n t)∘probe
noncomputable def regularValue : List Bool→List Bool := IntegralFramedBankTermCurrentQ.value (bank hn ht ha hR) (regularWord n t)∘probe

theorem mark_evaluator : SpaceFunction (markValue hn ht ha hR) :=
  (IntegralFramedBankTermCurrentQ.evaluator (bank hn ht ha hR) (IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR)
    _ (markWord_FP hn ht)).precompose probe probe_FP
theorem regular_evaluator : SpaceFunction (regularValue hn ht ha hR) :=
  (IntegralFramedBankTermCurrentQ.evaluator (bank hn ht ha hR) (IntegralMixedAuxiliaryMarkedIntegerPlan.bank_access hn ht ha hR)
    _ (regularWord_FP hn ht)).precompose probe probe_FP

noncomputable def language : Language := {q | q∈IntegralMixedMarkedLeafScan.language hn ht ha hR ∧
  regularValue hn ht ha hR q=InfinitesimalSign.encode 0 ∧ markValue hn ht ha hR q=InfinitesimalSign.encode 0}

theorem decider : SpaceDecider (language hn ht ha hR) := by
  have EL:=(IntegralMixedMarkedLeafScan.decider hn ht ha hR).flagEvaluator
  have ER:=(regular_evaluator hn ht ha hR).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EM:=(mark_evaluator hn ht ha hR).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (EL.andFlags (ER.andFlags EM)).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedMarkedPointTest

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedPlan
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Encoding.IntegralMixedMarkedPointTest
/-! # Native marked equations and all original leaves at one full vertex

Every control and original coefficient reader is derived from original
syntax. The only remaining boundary is the literal full-row backend.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents leafSource leafCount)
open IntegralMixedMarkedPointTest (markWord regularWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

noncomputable abbrev input :=IntegralFramedPhysicalBankTerm.input (bank hn ht ha hR outer)
def sampleContext (ctx : List Bool) :=pair ctx []
theorem sampleContext_FP : sampleContext∈FP :=mem_FP_pair id_mem_FP (constFn_mem_FP [])
def leafQuery (q : List Bool) :=pair (sampleContext (pairFst q)) (pairSnd q)
theorem leafQuery_FP : leafQuery∈FP :=mem_FP_pair (mem_FP_comp pairFst_mem_FP sampleContext_FP) pairSnd_mem_FP
def probe (q : List Bool) :=pair (leafQuery q) []
theorem probe_FP : probe∈FP :=mem_FP_pair leafQuery_FP (constFn_mem_FP [])

noncomputable def regularValue :=IntegralFramedPhysicalBankTerm.value (bank hn ht ha hR outer)
  (tables hn ht ha hR outer) (represents hn ht ha hR outer) (regularWord n t)∘probe
noncomputable def markValue :=IntegralFramedPhysicalBankTerm.value (bank hn ht ha hR outer)
  (tables hn ht ha hR outer) (represents hn ht ha hR outer) (markWord n t)∘probe
noncomputable def leaves : Language := {q | leafQuery q∈IntegralFramedPhysicalIntegerLeaves.language
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive
  (leafSource hn ht ha (R:=R) outer) (leafCount n outer)}
noncomputable def language : Language := {q |q∈leaves hn ht ha hR outer ∧
  regularValue hn ht ha hR outer q=InfinitesimalSign.encode 0 ∧ markValue hn ht ha hR outer q=InfinitesimalSign.encode 0}

attribute [local irreducible] regularValue markValue IntegralFramedPhysicalBankTerm.value bank tables

variable (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer)))

include ER in
theorem regular_evaluator : SpaceFunction (regularValue hn ht ha hR outer) :=by
  unfold regularValue
  exact (IntegralFramedPhysicalBankTerm.evaluator (bank hn ht ha hR outer) (tables hn ht ha hR outer)
    (represents hn ht ha hR outer) (native hn ht ha hR outer) (tables_native hn ht ha hR outer)
    (regularWord n t) (IntegralMixedMarkedPointTest.regularWord_FP hn ht) ER).precompose probe probe_FP
include ER in
theorem mark_evaluator : SpaceFunction (markValue hn ht ha hR outer) :=by
  unfold markValue
  exact (IntegralFramedPhysicalBankTerm.evaluator (bank hn ht ha hR outer) (tables hn ht ha hR outer)
    (represents hn ht ha hR outer) (native hn ht ha hR outer) (tables_native hn ht ha hR outer)
    (markWord n t) (IntegralMixedMarkedPointTest.markWord_FP hn ht) ER).precompose probe probe_FP
include ER in
theorem leaves_decider : SpaceDecider (leaves hn ht ha hR outer) :=by
  let A:=native hn ht ha hR outer
  exact (IntegralFramedPhysicalIntegerLeaves.decider
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
    (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (bank hn ht ha hR outer).positive
    (leafSource hn ht ha (R:=R) outer) (leafCount n outer)
    A.parameters (tables hn ht ha hR outer) (tables_native hn ht ha hR outer) (represents hn ht ha hR outer)
    A.liftedData A.controls A.bounds A.nodes A.factor A.seed A.key
    (IntegralMixedPhysicalMarkedPlan.leafSource_access hn ht ha hR outer)
    (IntegralMixedPhysicalMarkedPlan.leafCount_unary hn outer) ER).precompose leafQuery leafQuery_FP
include ER in
theorem decider : SpaceDecider (language hn ht ha hR outer) :=by
  have EL:=(leaves_decider hn ht ha hR outer ER).flagEvaluator
  have EF:=(regular_evaluator hn ht ha hR outer ER).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EM:=(mark_evaluator hn ht ha hR outer ER).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (EL.andFlags (EF.andFlags EM)).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq]
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedTest

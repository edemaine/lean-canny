/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicSignature
public import LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualityList
/-! # Native identity edges compare every actual atomic coordinate

Different histories, depths and own sample words are allowed. Candidate
bytes are fixed and every coordinate producer is compared by the native scan.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def left (z : List Bool):=pairFst z
def right (z : List Bool):=pairSnd z
theorem left_FP : left∈FP:=pairFst_mem_FP
theorem right_FP : right∈FP:=pairSnd_mem_FP

def SameProvider (z : List Bool):=FormulaSignSlotRadialProviderAtomic.provider (left z)=FormulaSignSlotRadialProviderAtomic.provider (right z)
theorem sameProvider_FP : FPPred SameProvider:=Brackets.stringEq_fppred
  (mem_FP_comp left_FP FormulaSignSlotRadialProviderAtomic.provider_FP)
  (mem_FP_comp right_FP FormulaSignSlotRadialProviderAtomic.provider_FP)

local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "I"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

noncomputable def ownSignature (q : List Bool):=FormulaSignSlotRadialProviderAtomic.signature (D q) (I q) q
noncomputable def table (z : List Bool):=IntegralMixedPhysicalPointSignatureComparison.pairs (D (left z))
  (ownSignature (left z)) (ownSignature (right z))
noncomputable def query (z : List Bool):=FormulaSignSlotRadialProviderFieldEqualityList.packet
  (FormulaSignSlotRadialProviderAtomic.context (left z)) (FormulaSignSlotRadialProviderAtomic.word (left z))
  (FormulaSignSlotRadialProviderAtomic.context (right z)) (FormulaSignSlotRadialProviderAtomic.word (right z)) (table z)

theorem table_FP : table∈FP:=IntegralMixedPhysicalPointSignatureComparison.pairs_FP
  ((FormulaSignSlotRadialProviderAtomic.dimension_unary).comp left_FP)
  (mem_FP_comp left_FP (FormulaSignSlotRadialProviderAtomic.native_signature))
  (mem_FP_comp right_FP (FormulaSignSlotRadialProviderAtomic.native_signature))
theorem query_FP : query∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp (f:=left) (g:=FormulaSignSlotRadialProviderAtomic.context) left_FP FormulaSignSlotRadialProviderAtomic.context_FP) (mem_FP_comp (f:=left) (g:=FormulaSignSlotRadialProviderAtomic.word) left_FP FormulaSignSlotRadialProviderAtomic.word_FP))
  (mem_FP_pair (mem_FP_pair (mem_FP_comp (f:=right) (g:=FormulaSignSlotRadialProviderAtomic.context) right_FP FormulaSignSlotRadialProviderAtomic.context_FP)
    (mem_FP_comp (f:=right) (g:=FormulaSignSlotRadialProviderAtomic.word) right_FP FormulaSignSlotRadialProviderAtomic.word_FP)) (table_FP))

noncomputable def language : Language:={z |SameProvider z∧
  FormulaSignSlotRadialProviderAtomic.Valid (left z)∧FormulaSignSlotRadialProviderAtomic.Valid (right z)∧
  query z∈FormulaSignSlotRadialProviderFieldEqualityList.language}

theorem decider : SpaceDecider (language):=by
  have EC:=SpaceFunction.ofFP _ sameProvider_FP.flag_mem_FP
  have EL:=(FormulaSignSlotRadialProviderAtomic.evaluator).precompose left left_FP
  have ER:=(FormulaSignSlotRadialProviderAtomic.evaluator).precompose right right_FP
  have EM:=((FormulaSignSlotRadialProviderFieldEqualityList.decider).precompose _ (query_FP)).flagEvaluator
  apply (EC.andFlags (EL.andFlags (ER.andFlags EM))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,Function.comp_apply,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

theorem dimension_eq (q : List Bool) : FormulaSignSlotRadialProviderAtomic.dimension q=
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialProviderAtomic.original q)+3 := by
  unfold FormulaSignSlotRadialProviderAtomic.dimension
  change LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension
    (FormulaSignSlotRadialProviderIntegerPlan.original
      (FormulaSignSlotRadialProviderRecordPlan.providerContext (FormulaSignSlotRadialProviderAtomic.root q)))+3=_
  rw [FormulaSignSlotRadialProviderAtomic.root_provider]
  rfl

theorem dimension_eq_of_providers (a b : List Bool)
    (hc : FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b) : D a=D b := by
  rw [dimension_eq,dimension_eq]
  exact congrArg (fun c : List Bool=>
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.dimension (FormulaSignSlotRadialExternalContext.original c)+3) hc

end LeanCanny.Encoding.FormulaSignSlotRadialProviderIdentity

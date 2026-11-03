/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicSignature
public import LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison
/-! # Native identity edges compare every actual atomic coordinate

Different histories, depths and own sample words are allowed. Candidate
bytes are fixed and every coordinate producer is compared by the native scan.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapIdentity
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def left (z : List Bool):=pairFst z
def right (z : List Bool):=pairSnd z
theorem left_FP : left∈FP:=pairFst_mem_FP
theorem right_FP : right∈FP:=pairSnd_mem_FP

def SameCandidate (z : List Bool):=IntegralMixedRoadmapAtomic.candidate (left z)=IntegralMixedRoadmapAtomic.candidate (right z)
theorem sameCandidate_FP : FPPred SameCandidate:=Brackets.stringEq_fppred
  (mem_FP_comp left_FP IntegralMixedRoadmapAtomic.candidate_FP)
  (mem_FP_comp right_FP IntegralMixedRoadmapAtomic.candidate_FP)

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

noncomputable def ownSignature (q : List Bool):=IntegralMixedRoadmapAtomic.signature (D q) (I q) q
noncomputable def table (z : List Bool):=IntegralMixedPhysicalPointSignatureComparison.pairs (D (left z))
  (ownSignature hn ht ha hR0 (left z)) (ownSignature hn ht ha hR0 (right z))
noncomputable def query (z : List Bool):=IntegralMixedPhysicalFieldEqualityList.packet
  (IntegralMixedRoadmapAtomic.context (left z)) (IntegralMixedRoadmapAtomic.word (left z))
  (IntegralMixedRoadmapAtomic.context (right z)) (IntegralMixedRoadmapAtomic.word (right z)) (table hn ht ha hR0 z)

theorem table_FP : table hn ht ha hR0∈FP:=IntegralMixedPhysicalPointSignatureComparison.pairs_FP
  ((IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0).comp left_FP)
  (mem_FP_comp left_FP (IntegralMixedRoadmapAtomic.native_signature hn ht ha hR0))
  (mem_FP_comp right_FP (IntegralMixedRoadmapAtomic.native_signature hn ht ha hR0))
theorem query_FP : query hn ht ha hR0∈FP:=mem_FP_pair
  (mem_FP_pair (mem_FP_comp (f:=left) (g:=IntegralMixedRoadmapAtomic.context) left_FP IntegralMixedRoadmapAtomic.context_FP) (mem_FP_comp (f:=left) (g:=IntegralMixedRoadmapAtomic.word) left_FP IntegralMixedRoadmapAtomic.word_FP))
  (mem_FP_pair (mem_FP_pair (mem_FP_comp (f:=right) (g:=IntegralMixedRoadmapAtomic.context) right_FP IntegralMixedRoadmapAtomic.context_FP)
    (mem_FP_comp (f:=right) (g:=IntegralMixedRoadmapAtomic.word) right_FP IntegralMixedRoadmapAtomic.word_FP)) (table_FP hn ht ha hR0))

noncomputable def language : Language:={z |SameCandidate z∧
  IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (left z)∧IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (right z)∧
  query hn ht ha hR0 z∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)}

theorem decider : SpaceDecider (language hn ht ha hR0):=by
  have EC:=SpaceFunction.ofFP _ sameCandidate_FP.flag_mem_FP
  have EL:=(IntegralMixedRoadmapAtomic.evaluator hn ht ha hR0).precompose left left_FP
  have ER:=(IntegralMixedRoadmapAtomic.evaluator hn ht ha hR0).precompose right right_FP
  have EM:=((IntegralMixedPhysicalFieldEqualityList.decider hn ht ha (radius_binary hR0)).precompose _ (query_FP hn ht ha hR0)).flagEvaluator
  apply (EC.andFlags (EL.andFlags (ER.andFlags EM))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,Function.comp_apply,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

theorem dimension_eq_of_candidates (a b : List Bool)
    (hc : IntegralMixedRoadmapAtomic.candidate a=IntegralMixedRoadmapAtomic.candidate b) : D a=D b :=by
  rw [IntegralMixedRoadmapAtomic.dimension_eq,IntegralMixedRoadmapAtomic.dimension_eq]
  exact congrArg (fun c : List Bool=>n (pairFst c)+3) hc

end LeanCanny.Encoding.IntegralMixedRoadmapIdentity

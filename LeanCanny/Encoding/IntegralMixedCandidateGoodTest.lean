/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReplayRelation
public import LeanCanny.Computation.SpaceFunctionWordExistence

/-! # The actual original candidate filter is decidable in polynomial space

A polynomial-width marked replay certifies the original zero equation. One
replay word supplies marked membership and the coordinate comparison together.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedCandidateGoodTest
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerPlan (radius_binary)
open IntegralMixedAuxiliaryMarkedNativeVertex (input input_access)
open IntegralMixedAuxiliaryMarkedCertifiedReplay (sampleContext)
open LeanCanny.Connectivity.AuxiliaryCandidateComponentCover (Good)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (q : List Bool) : List Bool := pair (pair (pairFst q) (pairSnd q)) []
theorem context_FP : context∈FP := by polytime [context]

def query (q : List Bool) : List Bool := pair (context (pairFst q)) (pairSnd q)
theorem query_FP : query∈FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP context_FP) pairSnd_mem_FP

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)

noncomputable def width (q : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (input hn ht ha (radius_binary hn ht ha)) (sampleContext (context q))

theorem width_unary : UnaryFn (width hn ht ha) :=
  (SquareSampleCompleteVertices.width_unary (input_access hn ht ha (radius_binary hn ht ha))).comp
    (mem_FP_pair context_FP (constFn_mem_FP []))

noncomputable def witnessLanguage : Language := {q | ∃w : List Bool,w.length=width hn ht ha q ∧
  pair (context q) w∈IntegralMixedMarkedReplayRelation.language hn ht ha (radius_binary hn ht ha)}

theorem witness_decider : SpaceDecider (witnessLanguage hn ht ha) := by
  have E:=((IntegralMixedMarkedReplayRelation.decider hn ht ha (radius_binary hn ht ha)).precompose query query_FP).flagEvaluator
  have W:=E.exists_words (width_unary hn ht ha)
  apply W.decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,query,pairFst_pair,pairSnd_pair,
    List.cons.injEq,and_true,decide_eq_true_eq]

def language : Language := {q | Good hn ht ha (pairFst q) (pairSnd q)}

theorem witness_iff (q : List Bool) : q∈witnessLanguage hn ht ha ↔q∈language hn ht ha :=
  (IntegralMixedMarkedReplayRelation.good_iff_exists hn ht ha (radius_binary hn ht ha)
    (pairFst q) (pairSnd q) []
    (IntegralMixedAuxiliaryMarkedCandidateAtRadius.native_radius_le hn ht ha (pairFst q) (pairSnd q) [])).symm

theorem decider : SpaceDecider (language hn ht ha) :=
  (witness_decider hn ht ha).congr (Set.ext (witness_iff hn ht ha))

theorem mem_PSPACE : language hn ht ha∈PSPACE := (decider hn ht ha).mem_PSPACE

theorem packet (u label : List Bool) : pair u label∈language hn ht ha ↔Good hn ht ha u label := by
  simp only [language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralMixedCandidateGoodTest

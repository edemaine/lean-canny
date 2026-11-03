/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Bounded own-root coordinate witnesses for one proper edge

Each coordinate searches its own ordinary and mean full words. Their widths
come from the actual prepared contexts. The rank has the original scalar
width; no complete certificate table or sampling oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def key (u : List Bool):=pairFst (pairFst (pairFst u))
def rank (u : List Bool):=pairSnd (pairFst (pairFst u))
def ordinary (u : List Bool):=pairSnd (pairFst u)
def mean (u : List Bool):=pairSnd u
def query (u : List Bool):=IntegralMixedRoadmapProperRowWitness.packet (key u) (ordinary u) (mean u) (rank u)
theorem query_FP : query∈FP:=by
  exact mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
      (mem_FP_pair pairSnd_mem_FP (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)))

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
 IntegralMixedRoadmapAtomic.width

noncomputable def fullWidth (mode : Bool) (z : List Bool):=
  SquareSampleCompleteVertices.width S (IntegralMixedRoadmapProperRow.context hn ht ha hR0 mode z)
noncomputable def rankWidth (z : List Bool):=IntegralMixedRoadmapAtomic.width hn ht ha hR0 (IntegralMixedRoadmapProperRow.atomic z)

theorem fullWidth_unary (mode : Bool) : UnaryFn (fullWidth hn ht ha hR0 mode):=
  (SquareSampleCompleteVertices.width_unary (IntegralMixedPhysicalMarkedNative.access hn ht ha (radius_binary hR0) false)).comp
    (IntegralMixedRoadmapProperRow.context_FP hn ht ha hR0 mode)
theorem rankWidth_unary : UnaryFn (rankWidth hn ht ha hR0):=
  (IntegralMixedRoadmapAtomic.width_unary hn ht ha hR0).comp IntegralMixedRoadmapProperRow.atomic_FP

noncomputable def Holds (right : Bool) (z : List Bool):=∃r : List Bool,r.length=rankWidth hn ht ha hR0 z∧
  ∃o : List Bool,o.length=fullWidth hn ht ha hR0 false z∧
  ∃m : List Bool,m.length=fullWidth hn ht ha hR0 true z∧
    IntegralMixedRoadmapProperRowWitness.packet z o m r∈IntegralMixedRoadmapProperRowWitness.language hn ht ha hR0 right
noncomputable def language (right : Bool) : Language:={z |Holds hn ht ha hR0 right z}

theorem evaluator (right : Bool) : SpaceFunction (fun z=>[decide (Holds hn ht ha hR0 right z)]):=by
  have E:=((IntegralMixedRoadmapProperRowWitness.decider hn ht ha hR0 right).precompose query query_FP).flagEvaluator
  have EM:=E.exists_words ((fullWidth_unary hn ht ha hR0 true).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  have EO:=EM.exists_words ((fullWidth_unary hn ht ha hR0 false).comp pairFst_mem_FP)
  have ER:=EO.exists_words (rankWidth_unary hn ht ha hR0)
  exact ER.congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,Function.comp_apply,Set.mem_preimage,query,key,rank,ordinary,mean,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider (right : Bool) : SpaceDecider (language hn ht ha hR0 right):=by
  apply (evaluator hn ht ha hR0 right).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch

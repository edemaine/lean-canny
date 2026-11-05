/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowWitness
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Bounded own-root coordinate witnesses for one proper edge

Each coordinate searches its own ordinary and mean full words. Their widths
come from the actual prepared contexts. The rank has the original scalar
width; no complete certificate table or sampling oracle is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateSearch
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def key (u : List Bool):=pairFst (pairFst (pairFst u))
def rank (u : List Bool):=pairSnd (pairFst (pairFst u))
def ordinary (u : List Bool):=pairSnd (pairFst u)
def mean (u : List Bool):=pairSnd u
def query (u : List Bool):=FormulaSignSlotRadialProviderProperRowWitness.packet (key u) (ordinary u) (mean u) (rank u)
theorem query_FP : query∈FP:=by
  exact mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
      (mem_FP_pair pairSnd_mem_FP (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)))

local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
 FormulaSignSlotRadialProviderAtomic.width

noncomputable def fullWidth (mode : Bool) (z : List Bool):=
  SquareSampleCompleteVertices.width S (FormulaSignSlotRadialProviderProperRow.context mode z)
noncomputable def rankWidth (z : List Bool):=FormulaSignSlotRadialProviderAtomic.width (FormulaSignSlotRadialProviderProperRow.atomic z)

theorem fullWidth_unary (mode : Bool) : UnaryFn (fullWidth mode):=
  (SquareSampleCompleteVertices.width_unary (FormulaSignSlotRadialProviderAtomic.input_access)).comp
    (FormulaSignSlotRadialProviderProperRow.context_FP mode)
theorem rankWidth_unary : UnaryFn (rankWidth):=
  (FormulaSignSlotRadialProviderAtomic.width_unary).comp FormulaSignSlotRadialProviderProperRow.atomic_FP

noncomputable def Holds (right : Bool) (z : List Bool):=∃r : List Bool,r.length=rankWidth z∧
  ∃o : List Bool,o.length=fullWidth false z∧
  ∃m : List Bool,m.length=fullWidth true z∧
    FormulaSignSlotRadialProviderProperRowWitness.packet z o m r∈FormulaSignSlotRadialProviderProperRowWitness.language right
noncomputable def language (right : Bool) : Language:={z |Holds right z}

theorem evaluator (right : Bool) : SpaceFunction (fun z=>[decide (Holds right z)]):=by
  have E:=((FormulaSignSlotRadialProviderProperRowWitness.decider right).precompose query query_FP).flagEvaluator
  have EM:=E.exists_words ((fullWidth_unary true).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP))
  have EO:=EM.exists_words ((fullWidth_unary false).comp pairFst_mem_FP)
  have ER:=EO.exists_words (rankWidth_unary)
  exact ER.congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,Function.comp_apply,Set.mem_preimage,query,key,rank,ordinary,mean,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider (right : Bool) : SpaceDecider (language right):=by
  apply (evaluator right).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateSearch

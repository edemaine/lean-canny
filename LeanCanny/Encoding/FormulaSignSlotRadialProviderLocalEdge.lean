/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCoordinateSearch
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperBase
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNoCritical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicValid
/-! # The entire native proper incidence predicate uses bounded searches

This assembles actual vertex, midpoint, order, no-bad/no-critical and every
coordinate guard. Its geometric path interpretation is proved separately.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderLocalEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def coordinateKey (u : List Bool):=pair (pairFst u) (BinaryNatCode.encode
  (FormulaSignSlotRadialProviderAtomic.depth (pairFst u)+(pairSnd u).length))
theorem coordinateKey_FP : coordinateKey∈FP:=mem_FP_pair pairFst_mem_FP
  (BinaryFn.ofUnary ((FormulaSignSlotRadialProviderAtomic.depth_unary.comp pairFst_mem_FP).add UnaryFn.index)).bits_mem_FP

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension

noncomputable def count (q : List Bool):=IntegralMixedRoadmapProper.captureCount
  (FormulaSignSlotRadialProviderAtomic.dimension q) q
theorem count_unary : UnaryFn (count):=
  IntegralMixedRoadmapProper.captureCount_unary (FormulaSignSlotRadialProviderAtomic.dimension_unary)
noncomputable def allCoordinates (right : Bool) (q : List Bool):=∀i<count q,
  FormulaSignSlotRadialProviderProperCoordinateSearch.Holds right (coordinateKey (pair q (List.replicate i true)))

theorem allCoordinates_evaluator (right : Bool) : SpaceFunction (fun q=>[decide (allCoordinates right q)]):=by
  have E:=((FormulaSignSlotRadialProviderProperCoordinateSearch.evaluator right).precompose
    coordinateKey coordinateKey_FP).forall_unary (count_unary)
  exact E.congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [allCoordinates,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def Local (q : List Bool):=FormulaSignSlotRadialProviderAtomic.Valid q∧
  FormulaSignSlotRadialProviderProper.Base q∧FormulaSignSlotRadialProviderProperCritical.NoCritical q∧
  (allCoordinates false q∨allCoordinates true q)
noncomputable def language : Language:={q |Local q}

theorem evaluator : SpaceFunction (fun q=>[decide (Local q)]):=by
  have HP:=(Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  have Hrows:=((allCoordinates_evaluator false).pairOutputs
    (allCoordinates_evaluator true)).postcompose _ HP.flag_mem_FP
  have ER : SpaceFunction (fun q=>[decide (allCoordinates false q∨allCoordinates true q)]):=
    Hrows.congr (funext fun q=>by
      simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])
  have EA:=FormulaSignSlotRadialProviderAtomic.evaluator
  have EB:=(FormulaSignSlotRadialProviderProper.base_decider).flagEvaluator
  have EC:=FormulaSignSlotRadialProviderProperCritical.noCritical_evaluator
  exact (EA.andFlags (EB.andFlags (EC.andFlags ER))).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Local,FormulaSignSlotRadialProviderProper.baseLanguage,Set.mem_ofPred_eq,
      List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language):=by
  apply (evaluator).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderLocalEdge

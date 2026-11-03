/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperCoordinateSearch
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBase
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNoCritical
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicVertex
/-! # The entire native proper incidence predicate uses bounded searches

This assembles actual vertex, midpoint, order, no-bad/no-critical and every
coordinate guard. Its geometric path interpretation is proved separately.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def coordinateKey (u : List Bool):=pair (pairFst u) (BinaryNatCode.encode
  (IntegralMixedRoadmapAtomic.depth (pairFst u)+(pairSnd u).length))
theorem coordinateKey_FP : coordinateKey∈FP:=mem_FP_pair pairFst_mem_FP
  (BinaryFn.ofUnary ((IntegralMixedRoadmapAtomic.depth_unary.comp pairFst_mem_FP).add UnaryFn.index)).bits_mem_FP

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedRoadmapAtomic.dimension

noncomputable def count (q : List Bool):=IntegralMixedRoadmapProper.captureCount
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q
theorem count_unary : UnaryFn (count hn ht ha hR0):=
  IntegralMixedRoadmapProper.captureCount_unary (IntegralMixedRoadmapAtomic.dimension_unary hn ht ha hR0)
noncomputable def allCoordinates (right : Bool) (q : List Bool):=∀i<count hn ht ha hR0 q,
  IntegralMixedRoadmapProperCoordinateSearch.Holds hn ht ha hR0 right (coordinateKey (pair q (List.replicate i true)))

theorem allCoordinates_evaluator (right : Bool) : SpaceFunction (fun q=>[decide (allCoordinates hn ht ha hR0 right q)]):=by
  have E:=((IntegralMixedRoadmapProperCoordinateSearch.evaluator hn ht ha hR0 right).precompose
    coordinateKey coordinateKey_FP).forall_unary (count_unary hn ht ha hR0)
  exact E.congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [allCoordinates,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def Local (q : List Bool):=IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q∧
  IntegralMixedRoadmapProper.Base hn ht ha hR0 q∧IntegralMixedRoadmapProperCritical.NoCritical hn ht ha hR0 q∧
  (allCoordinates hn ht ha hR0 false q∨allCoordinates hn ht ha hR0 true q)
noncomputable def language : Language:={q |Local hn ht ha hR0 q}

theorem evaluator : SpaceFunction (fun q=>[decide (Local hn ht ha hR0 q)]):=by
  have HP:=(Brackets.stringEq_fppred pairFst_mem_FP (constFn_mem_FP [true])).or
    (Brackets.stringEq_fppred pairSnd_mem_FP (constFn_mem_FP [true]))
  have Hrows:=((allCoordinates_evaluator hn ht ha hR0 false).pairOutputs
    (allCoordinates_evaluator hn ht ha hR0 true)).postcompose _ HP.flag_mem_FP
  have ER : SpaceFunction (fun q=>[decide (allCoordinates hn ht ha hR0 false q∨allCoordinates hn ht ha hR0 true q)]):=
    Hrows.congr (funext fun q=>by
      simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,List.cons.injEq,and_true,decide_eq_true_eq])
  have EA:=IntegralMixedRoadmapAtomic.evaluator hn ht ha hR0
  have EB:=(IntegralMixedRoadmapProper.base_decider hn ht ha hR0).flagEvaluator
  have EC:=IntegralMixedRoadmapProperCritical.noCritical_evaluator hn ht ha hR0
  exact (EA.andFlags (EB.andFlags (EC.andFlags ER))).congr (funext fun q=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Local,IntegralMixedRoadmapProper.baseLanguage,Set.mem_ofPred_eq,
      List.cons.injEq,and_true,decide_eq_true_eq])

theorem decider : SpaceDecider (language hn ht ha hR0):=by
  apply (evaluator hn ht ha hR0).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

end LeanCanny.Encoding.IntegralMixedRoadmapLocalEdge

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalReplayRelation
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardScan

/-! # Every actual critical correlation at one original full replay

The actual creating birth changes only the test datum. The original
marked context and full vertex word stay fixed throughout the scan.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalGuardScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem count_eq (c d : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (keyDatum (bank hn ht ha hR outer).key) (pair c d)=
        (input hn ht ha hR outer).count c :=by
  change _=IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan ((bank hn ht ha hR outer).key c))
  have HK : keyDatum (bank hn ht ha hR outer).key (pair c d)=(bank hn ht ha hR outer).key c :=
    congrArg (bank hn ht ha hR outer).key (pairFst_pair c d)
  exact (IntegralMixedFramedCriticalGuardBits.count_actual
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) (keyDatum (bank hn ht ha hR outer).key) (pair c d)).trans
      (congrArg (fun k=>IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
        (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan k)) HK)

noncomputable def scan : Language := IntegralFramedPhysicalCriticalGuardScan.language
  (input hn ht ha hR outer) (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
  (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (count_eq hn ht ha hR outer)

def probe (q : List Bool) :=pair (sampleContext (pairFst q)) (pairSnd q)
theorem probe_FP : probe∈FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP IntegralMixedPhysicalMarkedTest.sampleContext_FP) pairSnd_mem_FP

noncomputable def language : Language :={q |probe q∈scan hn ht ha hR outer}

attribute [local irreducible] bank tables scan

theorem decider (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceDecider (language hn ht ha hR outer) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  have E:=IntegralFramedPhysicalCriticalGuardScan.decider
    (input hn ht ha hR outer) B.parameters B.plan B.data (tables hn ht ha hR outer)
    B.nodes B.factor B.seed B.bounds B.key (count_eq hn ht ha hR outer)
    (IntegralMixedPhysicalReplayThom.input_access hn ht ha hR outer ER)
    A.parameters (tables_native hn ht ha hR outer) A.liftedData A.controls A.bounds
    A.nodes A.factor A.seed A.key
  unfold language scan
  exact E.precompose probe probe_FP

theorem packet (ctx w : List Bool) :
    pair ctx w∈language hn ht ha hR outer ↔
      SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w ∧
      IntegralFramedPhysicalCriticalGuardScan.holds
        (input hn ht ha hR outer) (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan
        (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
        (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
        (bank hn ht ha hR outer).bounds (bank hn ht ha hR outer).key (count_eq hn ht ha hR outer)
        (pair (sampleContext ctx) w) :=by
  simp only [language,probe,pairFst_pair,pairSnd_pair,scan,IntegralFramedPhysicalCriticalGuardScan.language,
    Set.mem_ofPred_eq]

noncomputable def relation : Language :={q |
  q∈IntegralMixedPhysicalReplayRelation.language hn ht ha hR outer ∧q∈language hn ht ha hR outer}

theorem relation_decider (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    SpaceDecider (relation hn ht ha hR outer) :=by
  have E:=(IntegralMixedPhysicalReplayRelation.decider hn ht ha hR outer ER).flagEvaluator
  have G:=(decider hn ht ha hR outer ER).flagEvaluator
  apply (E.andFlags G).decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [relation,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem sound (ctx w : List Bool) (h : pair ctx w∈relation hn ht ha hR outer) :
    IntegralMixedMarkedReplayRelation.originalZero hn ht ha (pairFst ctx) :=
  IntegralMixedPhysicalReplayRelation.sound hn ht ha hR outer ctx w h.1

theorem mem_PSPACE (ER : SpaceFunction (SquareSampleInput.rowCoefficient (input hn ht ha hR outer))) :
    relation hn ht ha hR outer∈PSPACE :=(relation_decider hn ht ha hR outer ER).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalGuardScan

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPointEquality
public import LeanCanny.Computation.SpaceFunctionQuantifiers
/-! # Every coordinate and selected scalar of a contiguous companion trace

The descriptor stores an anchor birth, first companion birth, and companion
count, all unary. Companion labels are chronological births, not raw columns.
The original full sampler context and word stay fixed through BOTH scans.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank native tables tables_native represents)
open IntegralFramedPhysicalCriticalGuardTest (keyDatum)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank native tables IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedPhysicalCriticalGuardTest.value IntegralMixedPhysicalPointEquality.value

def descriptor (a first number : ℕ) :=pair (List.replicate a true)
  (pair (List.replicate first true) (List.replicate number true))
def anchor (z : List Bool) :=(pairFst (pairSnd z)).length
def first (z : List Bool) :=(pairFst (pairSnd (pairSnd z))).length
def number (z : List Bool) :=(pairSnd (pairSnd (pairSnd z))).length
theorem anchor_unary : UnaryFn anchor:=UnaryFn.length (by polytime)
theorem first_unary : UnaryFn first:=UnaryFn.length (by polytime)
theorem number_unary : UnaryFn number:=UnaryFn.length (by polytime)
def canonical (z : List Bool) :=pair (pair (pairFst (pairFst z)) (pairSnd (pairFst z)))
  (descriptor (anchor z) (first z) (number z))
theorem canonical_FP : canonical∈FP:=mem_FP_pair (by polytime)
  (mem_FP_pair anchor_unary.mem_FP (mem_FP_pair first_unary.mem_FP number_unary.mem_FP))
def Wellformed (z : List Bool) :=z=canonical z
theorem wellformed_FP : FPPred Wellformed:=Brackets.stringEq_fppred id_mem_FP canonical_FP
theorem descriptor_packet (c w : List Bool) (a b k : ℕ) :
    Wellformed (pair (pair c w) (descriptor a b k)) :=by
  simp only [Wellformed,canonical,anchor,first,number,descriptor,pairFst_pair,pairSnd_pair,List.length_replicate]

def coordinateQuery (r : List Bool) :=
  let z:=pairFst (pairFst r)
  pair (pairFst z) (IntegralMixedPhysicalPointEquality.datum (anchor z)
    (first z+(pairSnd (pairFst r)).length) (pairSnd r).length)
theorem coordinateQuery_FP : coordinateQuery∈FP:=by
  have HZ : (fun r=>pairFst (pairFst r))∈FP:=by polytime
  have HA:=anchor_unary.comp HZ
  have HB:=(first_unary.comp HZ).add
    (UnaryFn.length (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
  exact mem_FP_pair (by polytime) (mem_FP_pair HA.mem_FP
    (mem_FP_pair HB.mem_FP (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP))
theorem coordinateQuery_packet (z : List Bool) (j i : ℕ) :
    coordinateQuery (pair (pair z (List.replicate j true)) (List.replicate i true))=
      pair (pairFst z) (IntegralMixedPhysicalPointEquality.datum (anchor z) (first z+j) i) :=by
  simp only [coordinateQuery,pairFst_pair,pairSnd_pair,List.length_replicate]
def correlationQuery (r : List Bool) :=pair (pairFst (pairFst r))
  (List.replicate (first (pairFst r)+(pairSnd r).length) true)
theorem correlationQuery_FP : correlationQuery∈FP:=mem_FP_pair (by polytime)
  ((first_unary.comp pairFst_mem_FP).add UnaryFn.index).mem_FP
def anchorQuery (z : List Bool) :=pair (pairFst (pairFst z)) (List.replicate (anchor z) true)
theorem anchorQuery_FP : anchorQuery∈FP:=mem_FP_pair (by polytime) anchor_unary.mem_FP

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "T" => tables hn ht ha hR outer
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
local notation "HC" => IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer

noncomputable def dimension (z : List Bool) :=(P).ambient (pairFst ((B).key (pairFst (pairFst z))))+1
theorem dimension_unary : UnaryFn (dimension hn ht ha hR outer) :=
  (((native hn ht ha hR outer).parameters.ambient.comp
    (mem_FP_comp (mem_FP_comp (by polytime) (native hn ht ha hR outer).key) pairFst_mem_FP)).add (UnaryFn.const 1))
noncomputable def Grammar (z : List Bool) :=Wellformed z ∧
  IntegralMixedFramedCriticalGuardBits.Active P T (keyDatum (B).key)
    IntegralFramedPhysicalCriticalGuardScan.stage (anchorQuery z) ∧
  first z+number z≤IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (pairFst (pairFst z)))
theorem grammar_FP : FPPred (Grammar hn ht ha hR outer) :=by
  have HA:=(IntegralMixedFramedCriticalGuardBits.active_FP P (native hn ht ha hR outer).parameters T
    (tables_native hn ht ha hR outer) (keyDatum (B).key) IntegralFramedPhysicalCriticalGuardScan.stage
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum_FP (B).key (native hn ht ha hR outer).key)
    IntegralFramedPhysicalCriticalGuardScan.stage_unary).comp anchorQuery_FP
  have HP : UnaryFn (fun z=>IntegralMixedFramedHistoryFamilyBits.prefixLength P ((B).key (pairFst (pairFst z)))):=
    (IntegralMixedFullHistoryFamilyBits.prefix_unary P (native hn ht ha hR outer).parameters).comp
      (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (native hn ht ha hR outer).key)
  exact wellformed_FP.and (HA.and ((BinaryFn.ofUnary (first_unary.add number_unary)).le (BinaryFn.ofUnary HP)))

noncomputable def correlation:=IntegralFramedPhysicalCriticalGuardTest.value S P (B).plan (B).data T
  (B).nodes (B).factor (B).seed (B).bounds (B).key IntegralFramedPhysicalCriticalGuardScan.stage HC∘correlationQuery
theorem correlation_evaluator : SpaceFunction (correlation hn ht ha hR outer) :=by
  unfold correlation
  exact (IntegralFramedPhysicalCriticalGuardTest.evaluator S P (B).plan (B).data T
    (B).nodes (B).factor (B).seed (B).bounds (B).key IntegralFramedPhysicalCriticalGuardScan.stage HC
    (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer) (native hn ht ha hR outer).parameters
    (tables_native hn ht ha hR outer) (native hn ht ha hR outer).liftedData
    (native hn ht ha hR outer).controls (native hn ht ha hR outer).bounds
    (native hn ht ha hR outer).nodes (native hn ht ha hR outer).factor (native hn ht ha hR outer).seed
    (native hn ht ha hR outer).key IntegralFramedPhysicalCriticalGuardScan.stage_unary).precompose
      correlationQuery correlationQuery_FP

noncomputable def holds (z : List Bool) : Prop :=∀j<number z,
  (∀i<dimension hn ht ha hR outer z,IntegralMixedPhysicalPointEquality.Accepted hn ht ha hR outer
    (coordinateQuery (pair (pair z (List.replicate j true)) (List.replicate i true)))) ∧
  correlation hn ht ha hR outer (pair z (List.replicate j true))=InfinitesimalSign.encode 0
theorem holds_evaluator : SpaceFunction (fun z=>[decide (holds hn ht ha hR outer z)]) :=by
  have EC:=(IntegralMixedPhysicalPointEquality.accepted_evaluator hn ht ha hR outer).precompose
    coordinateQuery coordinateQuery_FP
  have EI:=EC.forall_unary ((dimension_unary hn ht ha hR outer).comp pairFst_mem_FP)
  have ES:=(correlation_evaluator hn ht ha hR outer).postcompose
    (fun v=>[decide (v=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  exact ((EI.andFlags ES).forall_unary number_unary).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,pairFst_pair,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def language : Language:={z |SquareSampleCompleteVertices.Valid S (pairFst (pairFst z))
  (pairSnd (pairFst z)) ∧ Grammar hn ht ha hR outer z ∧ holds hn ht ha hR outer z}
theorem decider : SpaceDecider (language hn ht ha hR outer) :=by
  have EV:=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)).precompose
    pairFst pairFst_mem_FP).flagEvaluator
  have EG:=SpaceFunction.ofFP _ (grammar_FP hn ht ha hR outer).flag_mem_FP
  apply (EV.andFlags (EG.andFlags (holds_evaluator hn ht ha hR outer))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language hn ht ha hR outer∈PSPACE :=(decider hn ht ha hR outer).mem_PSPACE

end LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedFullCutOpenInterval
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
/-! # Original-only full cut-factor endpoint comparisons

The context is (original root, (unary creating birth, (left index,right index))).
The second outer field is the ONE complete full sampler word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutOpenInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalMarkedPlan (bank native controls tables tables_native represents)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

attribute [local irreducible] bank native controls tables IntegralMixedFramedHistoryFamilyBits.family

def birthWord (q : List Bool) :=pairFst (pairSnd q)
def selected (right : Bool) (q : List Bool) :=
  Nat.fromBitsLE (if right then pairSnd (pairSnd (pairSnd q)) else pairFst (pairSnd (pairSnd q)))
theorem selected_binary (right : Bool) : BinaryFn (selected right) :=by
  cases right <;> exact BinaryFn.fromBits (by polytime)

noncomputable def parent (q : List Bool) :=IntegralFramedTraceCutTask.task
  (bank hn ht ha hR outer).parameters (pair (pairFst q) (pair (birthWord q) []))
theorem parent_FP : parent hn ht ha hR outer∈FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (by polytime [birthWord]) (constFn_mem_FP [])))
    (IntegralFramedTraceCutTask.task_FP _ (native hn ht ha hR outer).parameters)
def guardContext (q : List Bool) :=pair (pair (pairFst q) []) (birthWord q)
theorem guardContext_FP : guardContext∈FP :=by polytime [guardContext,birthWord]
noncomputable def degree :=IntegralFramedTraceCutGuards.degree
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data∘guardContext
theorem degree_binary : BinaryFn (degree hn ht ha hR outer) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  have HD : BinaryFn (IntegralFramedTraceCutGuards.degree B.parameters B.plan B.data) :=
    IntegralFramedTraceCutGuards.degree_binary B.parameters A.parameters B.plan B.data
      (controls hn ht ha hR outer).normalization
  exact HD.comp guardContext_FP

noncomputable def comparison :=IntegralFramedFullCutOpenInterval.language
  (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
  (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
  (bank hn ht ha hR outer).bounds (parent hn ht ha hR outer) (bank hn ht ha hR outer).key
  (degree hn ht ha hR outer) (selected false) (selected true) (bank hn ht ha hR outer).positive
  (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
  (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer)

attribute [local irreducible] parent degree

private theorem endpoint_evaluator (right negative : Bool) :
    SpaceFunction (IntegralFramedFullCutOpenInterval.endpoint
      (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor (bank hn ht ha hR outer).seed
      (bank hn ht ha hR outer).bounds (parent hn ht ha hR outer) (bank hn ht ha hR outer).key
      (degree hn ht ha hR outer) (bank hn ht ha hR outer).positive
      (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer) (selected right) negative) :=by
  let B:=bank hn ht ha hR outer
  let A:=native hn ht ha hR outer
  have E:=IntegralFramedFullCutIntervalStatistic.evaluator B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds (parent hn ht ha hR outer) B.key
    (degree hn ht ha hR outer) (selected right) B.positive
    A.parameters A.nodes A.factor A.seed
    (IntegralMixedPhysicalTraceCutTest.probeControls hn ht ha hR outer)
    (IntegralMixedPhysicalTraceCutTest.probeBounds hn ht ha hR outer)
    A.liftedData A.controls A.bounds (tables hn ht ha hR outer) (tables_native hn ht ha hR outer)
    (represents hn ht ha hR outer) (parent_FP hn ht ha hR outer) A.key
    (degree_binary hn ht ha hR outer) (selected_binary right)
    (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer) 1 negative
  exact E.precompose (fun z=>pair z []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))

theorem comparison_decider : SpaceDecider (comparison hn ht ha hR outer) :=by
  unfold comparison
  exact IntegralFramedFullCutOpenInterval.decider_of_endpoints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (degree_binary hn ht ha hR outer) (endpoint_evaluator hn ht ha hR outer false true)
      (endpoint_evaluator hn ht ha hR outer true false)

def guardPacket (z : List Bool) :=pair
  (pair (pairFst (pairFst z)) (pairSnd z)) (birthWord (pairFst z))
theorem guardPacket_FP : guardPacket∈FP :=by polytime [guardPacket,birthWord]
noncomputable def count (q : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey (bank hn ht ha hR outer).parameters
    (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data ((bank hn ht ha hR outer).key q)).count
theorem count_unary : UnaryFn (count hn ht ha hR outer) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary _ (native hn ht ha hR outer).parameters _ _).comp
    (native hn ht ha hR outer).key
noncomputable def Bounds (z : List Bool) : Prop :=
  selected false (pairFst z)<count hn ht ha hR outer (pairFst z) ∧
  selected true (pairFst z)<count hn ht ha hR outer (pairFst z) ∧
  (birthWord (pairFst z)).length<count hn ht ha hR outer (pairFst z) ∧
  IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR outer (guardPacket z)
theorem bounds_FP : FPPred (Bounds hn ht ha hR outer) :=by
  have HC : BinaryFn (fun z=>count hn ht ha hR outer (pairFst z)):=
    (BinaryFn.ofUnary (count_unary hn ht ha hR outer)).comp pairFst_mem_FP
  have HL : BinaryFn (fun z=>selected false (pairFst z)) :=(selected_binary false).comp pairFst_mem_FP
  have HR : BinaryFn (fun z=>selected true (pairFst z)) :=(selected_binary true).comp pairFst_mem_FP
  have HS : UnaryFn (fun z=>(birthWord (pairFst z)).length):=UnaryFn.length (by polytime [birthWord])
  exact (HL.lt HC).and ((HR.lt HC).and (((BinaryFn.ofUnary HS).lt HC).and
    ((IntegralMixedPhysicalTraceCutScan.stageCut_FP hn ht ha hR outer).comp guardPacket_FP)))
noncomputable def language : Language := {z |
  z∈comparison hn ht ha hR outer ∧
  SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) (pairFst z) (pairSnd z) ∧
  Bounds hn ht ha hR outer z ∧
  IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (guardPacket z)}

theorem decider : SpaceDecider (language hn ht ha hR outer) :=by
  have EC:=(comparison_decider hn ht ha hR outer).flagEvaluator
  have EV:=(SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR outer)).flagEvaluator
  have EB:=SpaceFunction.ofFP _ (bounds_FP hn ht ha hR outer).flag_mem_FP
  have EG:=(IntegralMixedPhysicalTraceCutGuards.evaluator hn ht ha hR outer
    (IntegralMixedPhysicalMarkedNative.row_evaluator hn ht ha hR outer)).precompose guardPacket guardPacket_FP
  apply (EC.andFlags (EV.andFlags (EB.andFlags EG))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Function.comp_apply,
    List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language hn ht ha hR outer∈PSPACE :=(decider hn ht ha hR outer).mem_PSPACE

theorem degree_eq (q : List Bool) : degree hn ht ha hR outer q=
    (family (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data).degree
      (IntegralMixedVirtualTaskBits.saved (bank hn ht ha hR outer).parameters (parent hn ht ha hR outer q)) :=by
  simp only [degree,Function.comp_apply,IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.parent,
    IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,guardContext,
    pairFst_pair,pairSnd_pair,parent]

theorem degree_cap (q : List Bool) : degree hn ht ha hR outer q≤
    numericCap (bank hn ht ha hR outer).parameters (RankedHistoryTask.root (parent hn ht ha hR outer q)) :=by
  let B:=bank hn ht ha hR outer
  let G:=family B.parameters B.plan B.data
  let old:=IntegralMixedVirtualTaskBits.saved B.parameters (parent hn ht ha hR outer q)
  rw [degree_eq hn ht ha hR outer q]
  exact ((G.degree_bound old).trans (G.scalar_cap old)).trans
    (IntegralMixedValueTaskBounds.scalar_le_root_cap B.parameters G
      (IntegralMixedFramedHistoryFamilyBits.geometry B.parameters B.plan B.data) (parent hn ht ha hR outer q))

theorem language_iff_comparison (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
    (hb : Bounds hn ht ha hR outer (pair q w))
    (hg : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (guardPacket (pair q w))) :
    pair q w∈language hn ht ha hR outer ↔ pair q w∈comparison hn ht ha hR outer :=by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h,?_,hb,hg⟩
    simpa only [pairFst_pair,pairSnd_pair] using hv

theorem reject_left (z : List Bool)
    (hbad : count hn ht ha hR outer (pairFst z)≤selected false (pairFst z)) :
    z∉language hn ht ha hR outer :=by
  intro hz
  exact (Nat.not_lt_of_ge hbad) hz.2.2.1.1

end LeanCanny.Encoding.IntegralMixedPhysicalCutOpenInterval

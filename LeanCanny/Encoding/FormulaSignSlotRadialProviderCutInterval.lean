/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedFullCutOpenInterval
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicBeforeProbe
public import LeanCanny.Encoding.IntegralFramedPhysicalBankOrderSource
/-! # Actual provider full cut-factor endpoint comparisons

The context is (original root, (unary creating birth, (left index,right index))).
The second outer field is the ONE complete full sampler word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralFramedFullCutOpenInterval.language IntegralFramedFullCutOpenInterval.endpoint
  IntegralFramedPhysicalBankOrderSource.value IntegralFramedTraceCutGuards.choice
  IntegralFramedTraceCutGuards.degree
def birthWord (q : List Bool) :=pairFst (pairSnd q)
def selected (right : Bool) (q : List Bool) :=
  Nat.fromBitsLE (if right then pairSnd (pairSnd (pairSnd q)) else pairFst (pairSnd (pairSnd q)))
theorem selected_binary (right : Bool) : BinaryFn (selected right) :=by
  cases right <;> exact BinaryFn.fromBits (by polytime)

noncomputable def parent (q : List Bool) :=IntegralFramedTraceCutTask.task
  (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (pair (pairFst q) (pair (birthWord q) []))
theorem parent_FP : parent∈FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_pair
    (by polytime [birthWord]) (constFn_mem_FP [])))
    (IntegralFramedTraceCutTask.task_FP _ (FormulaSignSlotRadialProviderRecordPlan.bank_access).parameters)
def guardContext (q : List Bool) :=pair (pair (pairFst q) []) (birthWord q)
theorem guardContext_FP : guardContext∈FP :=by polytime [guardContext,birthWord]
noncomputable def degree :=IntegralFramedTraceCutGuards.degree
  (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data∘guardContext
theorem degree_binary : BinaryFn (degree) :=by
  let B:=FormulaSignSlotRadialProviderRecordPlan.bank
  let A:=FormulaSignSlotRadialProviderRecordPlan.bank_access
  have HD : BinaryFn (IntegralFramedTraceCutGuards.degree B.parameters B.plan B.data) :=
    IntegralFramedTraceCutGuards.degree_binary B.parameters A.parameters B.plan B.data
      FormulaSignSlotRadialProviderAtomic.Cuts.normalization
  exact HD.comp guardContext_FP

attribute [local irreducible] parent degree

noncomputable def comparison :=IntegralFramedFullCutOpenInterval.language
  (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data
  (FormulaSignSlotRadialProviderRecordPlan.bank).nodes (FormulaSignSlotRadialProviderRecordPlan.bank).factor (FormulaSignSlotRadialProviderRecordPlan.bank).seed
  (FormulaSignSlotRadialProviderRecordPlan.bank).bounds (parent) (FormulaSignSlotRadialProviderRecordPlan.bank).key
  (degree) (selected false) (selected true) (FormulaSignSlotRadialProviderRecordPlan.bank).positive
  (FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive)
  (FormulaSignSlotRadialProviderAtomic.Cuts.fallback)



private theorem endpoint_evaluator (right negative : Bool) :
    SpaceFunction (IntegralFramedFullCutOpenInterval.endpoint
      (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data
      (FormulaSignSlotRadialProviderRecordPlan.bank).nodes (FormulaSignSlotRadialProviderRecordPlan.bank).factor (FormulaSignSlotRadialProviderRecordPlan.bank).seed
      (FormulaSignSlotRadialProviderRecordPlan.bank).bounds (parent) (FormulaSignSlotRadialProviderRecordPlan.bank).key
      (degree) (FormulaSignSlotRadialProviderRecordPlan.bank).positive
      (FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive)
      (FormulaSignSlotRadialProviderAtomic.Cuts.fallback) (selected right) negative) :=by
  let B:=FormulaSignSlotRadialProviderRecordPlan.bank
  let A:=FormulaSignSlotRadialProviderRecordPlan.bank_access
  have E:=IntegralFramedFullCutIntervalStatistic.evaluator B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds (parent) B.key
    (degree) (selected right) B.positive
    A.parameters A.nodes A.factor A.seed
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeControls)
    (FormulaSignSlotRadialProviderAtomic.Cuts.probeBounds)
    A.liftedData A.controls A.bounds (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderRecordPlan.tables_native)
    (FormulaSignSlotRadialProviderAtomic.bank_represents) (parent_FP) A.key
    (degree_binary) (selected_binary right)
    (FormulaSignSlotRadialProviderAtomic.input_access)
    (FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive)
    (FormulaSignSlotRadialProviderAtomic.Cuts.fallback) 1 negative
  unfold IntegralFramedFullCutOpenInterval.endpoint
  exact E.precompose (fun z=>pair z []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))

theorem comparison_decider : SpaceDecider (comparison) :=by
  unfold comparison
  exact IntegralFramedFullCutOpenInterval.decider_of_endpoints _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (degree_binary) (endpoint_evaluator false true)
      (endpoint_evaluator true false)

def guardPacket (z : List Bool) :=pair
  (pair (pairFst (pairFst z)) (pairSnd z)) (birthWord (pairFst z))
theorem guardPacket_FP : guardPacket∈FP :=by polytime [guardPacket,birthWord]
noncomputable def count (q : List Bool) :=
  (IntegralMixedFramedBankSnapshotBits.atKey (FormulaSignSlotRadialProviderRecordPlan.bank).parameters
    (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data ((FormulaSignSlotRadialProviderRecordPlan.bank).key q)).count
theorem count_unary : UnaryFn (count) :=
  (IntegralMixedFramedBankSnapshotBits.count_unary _ (FormulaSignSlotRadialProviderRecordPlan.bank_access).parameters _ _).comp
    (FormulaSignSlotRadialProviderRecordPlan.bank_access).key
noncomputable def Bounds (z : List Bool) : Prop :=
  selected false (pairFst z)<count (pairFst z) ∧
  selected true (pairFst z)<count (pairFst z) ∧
  (birthWord (pairFst z)).length<count (pairFst z) ∧
  FormulaSignSlotRadialProviderAtomic.Cuts.StageCut (guardPacket z)
theorem bounds_FP : FPPred (Bounds) :=by
  have HC : BinaryFn (fun z=>count (pairFst z)):=
    (BinaryFn.ofUnary (count_unary)).comp pairFst_mem_FP
  have HL : BinaryFn (fun z=>selected false (pairFst z)) :=(selected_binary false).comp pairFst_mem_FP
  have HR : BinaryFn (fun z=>selected true (pairFst z)) :=(selected_binary true).comp pairFst_mem_FP
  have HS : UnaryFn (fun z=>(birthWord (pairFst z)).length):=UnaryFn.length (by polytime [birthWord])
  exact (HL.lt HC).and ((HR.lt HC).and (((BinaryFn.ofUnary HS).lt HC).and
    ((FormulaSignSlotRadialProviderAtomic.Cuts.stageCut_FP).comp guardPacket_FP)))
theorem degree_eq (q : List Bool) : degree q=
    (family (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data).degree
      (IntegralMixedVirtualTaskBits.saved (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (parent q)) :=by
  simp only [degree,Function.comp_apply,IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.parent,
    IntegralFramedTraceCutGuards.descriptor,IntegralFramedTraceCutGuards.root,guardContext,
    pairFst_pair,pairSnd_pair,parent]

theorem degree_cap (q : List Bool) : degree q≤
    numericCap (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (RankedHistoryTask.root (parent q)) :=by
  let B:=FormulaSignSlotRadialProviderRecordPlan.bank
  let G:=family B.parameters B.plan B.data
  let old:=IntegralMixedVirtualTaskBits.saved B.parameters (parent q)
  rw [degree_eq q]
  exact ((G.degree_bound old).trans (G.scalar_cap old)).trans
    (IntegralMixedValueTaskBounds.scalar_le_root_cap B.parameters G
      (IntegralMixedFramedHistoryFamilyBits.geometry B.parameters B.plan B.data) (parent q))


/-- Every coefficient query retains this literal full sampler context and word. -/
def signQuery (r : List Bool) := pair (pairFst r)
  (pair (birthWord (pairFst (pairFst r))) (pairSnd r))
theorem signQuery_FP : signQuery∈FP := by polytime [signQuery,birthWord]
noncomputable def sign := FormulaSignSlotRadialProviderAtomic.Cuts.value∘signQuery

def head (_ : List Bool) := InfinitesimalSign.encode 1
noncomputable def choice (z : List Bool) := IntegralFramedTraceCutGuards.choice
  FormulaSignSlotRadialProviderRecordPlan.bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank.plan
  FormulaSignSlotRadialProviderRecordPlan.bank.data (guardContext (pairFst z))
attribute [local irreducible] choice
theorem choice_binary : BinaryFn choice := by
  unfold choice
  exact   (IntegralFramedTraceCutGuards.choice_binary FormulaSignSlotRadialProviderRecordPlan.bank.parameters
    FormulaSignSlotRadialProviderRecordPlan.bank_access.parameters FormulaSignSlotRadialProviderRecordPlan.bank.plan
    FormulaSignSlotRadialProviderRecordPlan.bank.data FormulaSignSlotRadialProviderAtomic.Cuts.normalization).comp
      (mem_FP_comp pairFst_mem_FP guardContext_FP)
noncomputable def cap (z : List Bool) := 2^FormulaSignSlotRadialProviderRecordPlan.bank.parameters.width (pairFst (pairFst z))
noncomputable abbrev Guards (z : List Bool) := FiniteCoefficientSignScan.Guards sign head choice (degree∘pairFst) cap z

theorem guards_evaluator : SpaceFunction (fun z=>[decide (Guards z)]) := by
  have ES : SpaceFunction sign := FormulaSignSlotRadialProviderAtomic.Cuts.value_evaluator.precompose signQuery signQuery_FP
  have EH : SpaceFunction head := SpaceFunction.ofFP _ (constFn_mem_FP _)
  exact FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH choice_binary
    (degree_binary.comp pairFst_mem_FP)
    ((BinaryFn.const 2).powUnary (FormulaSignSlotRadialProviderRecordPlan.bank_access.parameters.width.comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)))

noncomputable def order (z : List Bool) := IntegralFramedPhysicalBankOrderSource.value
  FormulaSignSlotRadialProviderRecordPlan.bank (selected false) (selected true)
  FormulaSignSlotRadialProviderRecordPlan.tables FormulaSignSlotRadialProviderAtomic.bank_represents (pair z [])
theorem order_evaluator : SpaceFunction order := by
  have E := IntegralFramedPhysicalBankOrderSource.evaluator FormulaSignSlotRadialProviderRecordPlan.bank
    (selected false) (selected true) FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents FormulaSignSlotRadialProviderRecordPlan.bank_access
    FormulaSignSlotRadialProviderRecordPlan.tables_native (selected_binary false) (selected_binary true)
    FormulaSignSlotRadialProviderAtomic.row_evaluator
  exact E.precompose (fun z=>pair z []) (mem_FP_pair id_mem_FP (constFn_mem_FP []))

noncomputable def language : Language := {z | z∈comparison ∧
  SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (pairFst z) (pairSnd z) ∧
    Bounds z ∧ Guards z ∧ order z=InfinitesimalSign.encode 1}
theorem decider : SpaceDecider language := by
  have EC := comparison_decider.flagEvaluator
  have EV := (SquareSampleCompleteVertices.decider FormulaSignSlotRadialProviderAtomic.input_access).flagEvaluator
  have EB := SpaceFunction.ofFP _ bounds_FP.flag_mem_FP
  have EG := guards_evaluator
  have OD : SpaceDecider {z |order z=InfinitesimalSign.encode 1} := by
    apply order_evaluator.decider (fun v=>decide (v=InfinitesimalSign.encode 1))
      (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 1))).flag_mem_FP
    intro z
    simp only [Set.mem_ofPred_eq,decide_eq_true_eq]
  apply (EC.andFlags (EV.andFlags (EB.andFlags (EG.andFlags OD.flagEvaluator)))).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE
end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval

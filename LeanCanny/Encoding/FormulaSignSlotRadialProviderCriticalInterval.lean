/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankEquality
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalGuardTest
public import LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
public import LeanCanny.Computation.SpaceFunctionWordExistence
/-! # Native exhaustive full-joint search for a parent-correlated critical probe

Every complete child word is considered, including singular roots. The fixed
parent word and both interval endpoints belong to the same prepared target cap.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key key_birth positive input)
open IntegralMixedPhysicalCriticalQuery (parentWord leftWord rightWord)
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
noncomputable def withKeyBank (B : IntegralFramedBankQuery.Bank) (k : List Bool→List Bool)
    (hp : ∀q,0<(family B.parameters B.plan B.data).birth (k q)) : IntegralFramedBankQuery.Bank :=
  {B with key:=k,positive:=hp,coordinate q:=⟨0,hp q⟩}

noncomputable def withKeyAccess (B : IntegralFramedBankQuery.Bank) (A : IntegralFramedBankQuery.Access B)
    (k : List Bool→List Bool) (hk : k∈FP)
    (hp : ∀q,0<(family B.parameters B.plan B.data).birth (k q)) :
    IntegralFramedBankQuery.Access (withKeyBank B k hp) :=
  {A with key:=hk,coordinate:=UnaryFn.const 0}

noncomputable def childBank := withKeyBank FormulaSignSlotRadialProviderRecordPlan.bank (key true) (positive true)
noncomputable def childAccess : IntegralFramedBankQuery.Access childBank :=
  withKeyAccess FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.bank_access
    (key true) (FormulaSignSlotRadialProviderCriticalPrefixes.key_FP true) (positive true)

def tail (saved : List Bool) :=pairSnd (pairSnd saved)
def endpoint (right : Bool) (q : List Bool) :=if right then rightWord q else leftWord q
noncomputable def clipped (right : Bool) (q : List Bool) :=
  min (Nat.fromBitsLE (endpoint right q)) (birth false q)
theorem clipped_unary (right : Bool) : UnaryFn (clipped right) := by
  have HE : endpoint right∈FP :=by cases right <;> polytime [endpoint,rightWord,leftWord,IntegralMixedPhysicalCriticalQuery.root]
  exact UnaryFn.fromBitsLE_min HE (FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false)

noncomputable def term (upper : Bool) (original : List Bool) : Term :=
  if upper then .add (.var (clipped true (pair original [])))
    (.mul (.const (-1)) (.var (birth false (pair original []))))
  else .add (.var (birth false (pair original [])))
    (.mul (.const (-1)) (.var (clipped false (pair original []))))
noncomputable def word (upper : Bool) (saved : List Bool) :=(term upper saved).toData.toBits

theorem word_FP (upper : Bool) : word upper∈FP := by
  have HT : (fun q : List Bool=>pair q [])∈FP :=mem_FP_pair id_mem_FP (constFn_mem_FP [])
  have HN:=Term.variableBits_mem_FP ((FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false).comp HT)
  have HE (r : Bool):=Term.variableBits_mem_FP ((clipped_unary r).comp HT)
  have HK:=(constFn_mem_FP (Term.const (-1)).toData.toBits)
  cases upper
  · exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 HN (Codec.taggedTwo_mem_FP 3 HK (HE false)))
      (fun _=>by simp only [word,term,Term.variableBits_eq,Term.toData,Codec.taggedTwo_toBits];rfl)
  · exact mem_FP_of_eq (Codec.taggedTwo_mem_FP 2 (HE true) (Codec.taggedTwo_mem_FP 3 HK HN))
      (fun _=>by simp only [word,term,Term.variableBits_eq,Term.toData,Codec.taggedTwo_toBits];rfl)

def probe (z : List Bool) :=pair z []
theorem probe_FP : probe∈FP :=mem_FP_pair id_mem_FP (constFn_mem_FP [])
noncomputable def value (upper : Bool) :=IntegralFramedPhysicalBankTerm.value (childBank)
  (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderAtomic.bank_represents) (word upper)∘probe

attribute [local irreducible] childAccess value

theorem evaluator (upper : Bool) : SpaceFunction (value upper) :=by
  unfold value
  exact (IntegralFramedPhysicalBankTerm.evaluator (childBank)
    (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderAtomic.bank_represents) (childAccess)
    (FormulaSignSlotRadialProviderRecordPlan.tables_native) (word upper) (word_FP upper)
    (FormulaSignSlotRadialProviderCriticalPrefixes.row_evaluator true)).precompose probe probe_FP

theorem square_input_count (B : IntegralFramedBankQuery.Bank) (k : List Bool→List Bool)
    (hp : ∀q,0<(family B.parameters B.plan B.data).birth (k q)) (q : List Bool) :
    (IntegralFramedPhysicalSquare.input B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds k hp).count q=
      IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands B.parameters B.plan (k q)) := rfl

theorem guard_count (q d : List Bool) :
    IntegralMixedFramedCriticalGuardBits.count (FormulaSignSlotRadialProviderRecordPlan.bank).parameters
      (FormulaSignSlotRadialProviderRecordPlan.tables) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (pair q d)=
        (input true).count q :=by
  have E:=IntegralMixedFramedCriticalGuardBits.count_actual
    (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data
    (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderAtomic.bank_represents)
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (pair q d)
  have HK : IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true) (pair q d)=key true q :=
    congrArg (key true) (pairFst_pair q d)
  have HI := square_input_count FormulaSignSlotRadialProviderRecordPlan.bank (key true) (positive true) q
  exact (E.trans (congrArg (fun k=>IntegralMixedFramedPhysicalIndex.arity
    (IntegralMixedFramedHistoryFamilyBits.commands (FormulaSignSlotRadialProviderRecordPlan.bank).parameters
      (FormulaSignSlotRadialProviderRecordPlan.bank).plan k)) HK)).trans HI.symm

noncomputable def stage (z : List Bool) :=birth false (pairFst z)
noncomputable def correlation :=IntegralFramedPhysicalCriticalGuardTest.value (input true)
  (FormulaSignSlotRadialProviderRecordPlan.bank).parameters (FormulaSignSlotRadialProviderRecordPlan.bank).plan (FormulaSignSlotRadialProviderRecordPlan.bank).data
  (FormulaSignSlotRadialProviderRecordPlan.tables) (FormulaSignSlotRadialProviderRecordPlan.bank).nodes (FormulaSignSlotRadialProviderRecordPlan.bank).factor
  (FormulaSignSlotRadialProviderRecordPlan.bank).seed (FormulaSignSlotRadialProviderRecordPlan.bank).bounds (key true) (stage)
  (guard_count)∘probe

theorem correlation_evaluator : SpaceFunction (correlation) :=by
  let B:=FormulaSignSlotRadialProviderRecordPlan.bank
  let A:=FormulaSignSlotRadialProviderRecordPlan.bank_access
  exact (IntegralFramedPhysicalCriticalGuardTest.evaluator (input true)
    B.parameters B.plan B.data (FormulaSignSlotRadialProviderRecordPlan.tables) B.nodes B.factor B.seed B.bounds
    (key true) (stage) (guard_count)
    (FormulaSignSlotRadialProviderCriticalPrefixes.access true)
    A.parameters (FormulaSignSlotRadialProviderRecordPlan.tables_native) A.liftedData A.controls A.bounds A.nodes A.factor A.seed
    (FormulaSignSlotRadialProviderCriticalPrefixes.key_FP true)
    ((FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false).comp pairFst_mem_FP)).precompose probe probe_FP

noncomputable def Guard (q : List Bool) : Prop :=
  IntegralMixedPhysicalCriticalQuery.critical q ∧
    Nat.fromBitsLE (leftWord q)<birth false q ∧ Nat.fromBitsLE (rightWord q)<birth false q
theorem guard_FP : FPPred (Guard) :=
  IntegralMixedPhysicalCriticalQuery.critical_FP.and
    (((BinaryFn.fromBits (by polytime [leftWord,IntegralMixedPhysicalCriticalQuery.root])).lt
      (BinaryFn.ofUnary (FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false))).and
    ((BinaryFn.fromBits (by polytime [rightWord,IntegralMixedPhysicalCriticalQuery.root])).lt
      (BinaryFn.ofUnary (FormulaSignSlotRadialProviderCriticalPrefixes.birth_unary false))))

noncomputable def witnessLanguage : Language := {z |
  Guard (pairFst z) ∧
  SquareSampleCompleteVertices.Valid (input false) (pairFst z) (parentWord (pairFst z)) ∧
  SquareSampleCompleteVertices.Valid (input true) (pairFst z) (pairSnd z) ∧
  FormulaSignSlotRadialProviderCriticalBankEquality.agrees z ∧
  correlation z=InfinitesimalSign.encode 0 ∧
  value false z=InfinitesimalSign.encode 1 ∧
  value true z=InfinitesimalSign.encode 1}

theorem witness_decider : SpaceDecider (witnessLanguage) :=by
  have GP:=SpaceFunction.ofFP _ (((guard_FP).comp pairFst_mem_FP).flag_mem_FP)
  have P:=((SquareSampleCompleteVertices.decider (FormulaSignSlotRadialProviderCriticalPrefixes.access false)).precompose
    (fun z=>pair (pairFst z) (parentWord (pairFst z))) (by polytime [parentWord])).flagEvaluator
  have C:=(SquareSampleCompleteVertices.decider (FormulaSignSlotRadialProviderCriticalPrefixes.access true)).flagEvaluator
  have A:=FormulaSignSlotRadialProviderCriticalBankEquality.scanEvaluator
  have G:=(correlation_evaluator).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 0)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have L:=(evaluator false).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have U:=(evaluator true).postcompose (fun z=>[decide (z=InfinitesimalSign.encode 1)])
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  apply (GP.andFlags (P.andFlags (C.andFlags (A.andFlags (G.andFlags (L.andFlags U)))))).decider
    (fun z=>decide (z=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [witnessLanguage,Set.mem_ofPred_eq,Set.mem_preimage,SquareSampleCompleteVertices.language,
    pairFst_pair,pairSnd_pair,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq]

noncomputable def width (q : List Bool) :=SquareSampleCompleteVertices.width (input true) q
theorem width_unary : UnaryFn (width) :=
  SquareSampleCompleteVertices.width_unary (FormulaSignSlotRadialProviderCriticalPrefixes.access true)
noncomputable def language : Language := {q |∃w : List Bool,
  w.length=width q ∧ pair q w∈witnessLanguage}

theorem decider : SpaceDecider (language) :=by
  have E:=(witness_decider).flagEvaluator.exists_words (width_unary)
  apply E.decider (fun z=>decide (z=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language∈PSPACE :=(decider).mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval

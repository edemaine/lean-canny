/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicCutTest
public import LeanCanny.Encoding.IntegralFramedTraceCutScan
/-! # All meaningful source-aware cut guards share one complete own word -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Cuts
open LeanCanny.Algebra LeanCanny.Computation
open FormulaSignSlotRadialProviderAtomic (input input_access)
open IntegralFramedTraceCutScan (stagePacket stageQuery stageQuery_FP)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "A" => FormulaSignSlotRadialProviderRecordPlan.bank_access
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable def normalization : IntegralMixedFramedNormalizationBits.Controls
    (B).parameters (B).plan (B).data := by
  unfold FormulaSignSlotRadialProviderRecordPlan.bank
  exact FormulaSignSlotRadialProviderRecordPlan.certifiedControls.normalization

def creatingRoot := IntegralFramedTraceCutGuards.root
def ownWord := IntegralFramedTraceCutGuards.word
def creatingStage := IntegralFramedTraceCutGuards.stage
theorem creatingRoot_FP : creatingRoot∈FP := IntegralFramedTraceCutGuards.root_FP
theorem ownWord_FP : ownWord∈FP := IntegralFramedTraceCutGuards.word_FP
theorem creatingStage_unary : UnaryFn creatingStage := IntegralFramedTraceCutGuards.stage_unary

def coefficientQuery (z : List Bool) := pair
  (pair (pair (creatingRoot (pairFst z)) []) (ownWord (pairFst z)))
  (pair (pairSnd (pairFst z)) (pairSnd z))
theorem coefficientQuery_FP : coefficientQuery∈FP := by
  have HR := mem_FP_pair (mem_FP_comp pairFst_mem_FP creatingRoot_FP) (constFn_mem_FP [])
  have HW := mem_FP_comp pairFst_mem_FP ownWord_FP
  exact mem_FP_pair (mem_FP_pair HR HW)
    (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def age (b : List Bool) := FormulaSignSlotRadialProviderRecordPlan.fullCount (creatingRoot b)-creatingStage b-1
theorem age_unary : UnaryFn age :=
  ((FormulaSignSlotRadialProviderRecordPlan.fullCount_unary.comp creatingRoot_FP).sub creatingStage_unary).sub (UnaryFn.const 1)
noncomputable def column (b : List Bool) := IntegralMixedFramedPhysicalIndex.scalarColumn (B).parameters T
  (pair ((B).key (pair (creatingRoot b) [])) (BinaryNatCode.encode (age b)))
theorem column_unary : UnaryFn column :=
  (IntegralMixedFramedPhysicalIndex.scalarColumn_unary (B).parameters (A).parameters T
    FormulaSignSlotRadialProviderRecordPlan.tables_native).comp
      (mem_FP_pair (mem_FP_comp (mem_FP_pair creatingRoot_FP (constFn_mem_FP [])) (A).key)
        (BinaryFn.ofUnary age_unary).bits_mem_FP)
def sample (b : List Bool) := pair (pair (creatingRoot b) []) (ownWord b)
theorem sample_FP : sample∈FP := mem_FP_pair (mem_FP_pair creatingRoot_FP (constFn_mem_FP [])) ownWord_FP
noncomputable def headQuery (b : List Bool) := pair (sample b) (BinaryNatCode.encode (column b))
theorem headQuery_FP : headQuery∈FP := mem_FP_pair sample_FP (BinaryFn.ofUnary column_unary).bits_mem_FP
noncomputable def sign := value ∘coefficientQuery
noncomputable def head := SquareSampleCompleteCoordinateSign.value input ∘headQuery
noncomputable def Guards (b : List Bool) := FiniteCoefficientSignScan.Guards sign head
  (IntegralFramedTraceCutGuards.choice (B).parameters (B).plan (B).data)
  (IntegralFramedTraceCutGuards.degree (B).parameters (B).plan (B).data)
  (IntegralFramedTraceCutGuards.cap (B).parameters) b
attribute [local irreducible] sign head column age

theorem guards_evaluator : SpaceFunction (fun b => [decide (Guards b)]) := by
  have ES : SpaceFunction sign := by
    unfold sign
    exact value_evaluator.precompose coefficientQuery coefficientQuery_FP
  have EH : SpaceFunction head := by
    unfold head
    exact (SquareSampleCompleteCoordinateSign.evaluator input_access).precompose headQuery headQuery_FP
  have E := FiniteCoefficientSignScan.evaluator _ _ _ _ _ ES EH
    (IntegralFramedTraceCutGuards.choice_binary (B).parameters (A).parameters (B).plan (B).data
      normalization)
    (IntegralFramedTraceCutGuards.degree_binary (B).parameters (A).parameters (B).plan (B).data
      normalization)
    (IntegralFramedTraceCutGuards.cap_binary (B).parameters (A).parameters)
  exact E.congr (by
    funext b
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards,decide_eq_true_eq])

def StageCut (b : List Bool) := IntegralFramedTraceCutScan.StageCut (B).parameters (B).plan b
theorem stageCut_FP : FPPred StageCut := IntegralFramedTraceCutScan.stageCut_FP (B).parameters
  (A).parameters (B).plan (B).data normalization
attribute [local irreducible] Guards StageCut
noncomputable def holds (q : List Bool) := ∀j<FormulaSignSlotRadialProviderRecordPlan.fullCount (pairFst q)-1,
  StageCut (stagePacket q j) → Guards (stagePacket q j)
theorem holds_evaluator : SpaceFunction (fun q => [decide (holds q)]) := by
  have E := SpaceFunction.branch (fun b => decide (StageCut b)) stageCut_FP.flag_mem_FP
    guards_evaluator (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  have EI : SpaceFunction (fun b => [decide (StageCut b → Guards b)]) := E.congr (by
    funext b
    by_cases HB : StageCut b <;>
      simp only [HB,decide_true,decide_false,ite_true,Bool.false_eq_true,ite_false,
        true_implies,false_implies,decide_true])
  have EU := (EI.precompose stageQuery stageQuery_FP).forall_unary
    ((FormulaSignSlotRadialProviderRecordPlan.fullCount_unary.comp pairFst_mem_FP).sub (UnaryFn.const 1))
  exact EU.congr (by
    funext q
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Function.comp_apply,stageQuery,stagePacket,pairFst_pair,pairSnd_pair,
      List.cons.injEq,and_true,decide_eq_true_eq])

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.Cuts

namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

noncomputable def BeforeProbe (q : List Bool) := FullValid q ∧ Cuts.holds (fullQuery q)
theorem beforeProbe_decider : SpaceDecider {q | BeforeProbe q} := by
  have EV := full_decider.flagEvaluator
  have EH := Cuts.holds_evaluator.precompose fullQuery fullQuery_FP
  apply (EV.andFlags EH).decider (fun v => decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [BeforeProbe,Set.mem_ofPred_eq,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq]
theorem beforeProbe_PSPACE : {q | BeforeProbe q}∈PSPACE := beforeProbe_decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic

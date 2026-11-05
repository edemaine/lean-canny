/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceRawGuards
public import LeanCanny.Encoding.CoefficientMarkedRecordTraceStages
/-! # Every scanned creating cut is an actual original raw-record stage -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceStageBinding
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits IntegralMixedCommandHeaderBits IntegralFramedCreatingCut
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem stage_parent (P : Parameters) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.parent P (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
      IntegralFramedTraceCutTask.task P (pair ctx (pair (List.replicate j true) [])) := by
  simp only [IntegralFramedTraceCutGuards.parent, Function.comp_apply,
    IntegralFramedTraceCutGuards.descriptor, IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair]

private theorem stage_cut (P : Parameters) (D : Plan P) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutScan.StageCut P D (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) ↔
      IsCut (instruction P D (IntegralMixedVirtualTaskBits.saved P
        (IntegralFramedTraceCutTask.task P (pair ctx (pair (List.replicate j true) []))))).command := by
  unfold IntegralFramedTraceCutScan.StageCut IntegralFramedCreatingCut.ParentCut
  rw [stage_parent]

private theorem saved_stage (P : Parameters) (ctx : List Bool) (j : ℕ) (hj : j ≤ P.cap ctx+1) :
    IntegralMixedVirtualTaskBits.saved P (IntegralFramedTraceCutTask.task P
      (pair ctx (pair (List.replicate j true) []))) = keyAt ctx j (BinaryNatCode.encode 2) := by
  have hb : IntegralFramedTraceCutTask.stage (pair ctx (pair (List.replicate j true) [])) ≤
      birthCap P (pairFst (pair ctx (pair (List.replicate j true) []))) := by
    simpa only [IntegralFramedTraceCutTask.stage_packet, List.length_replicate, birthCap, pairFst_pair] using hj
  simpa only [pairFst_pair, IntegralFramedTraceCutTask.stage_packet, List.length_replicate] using
    IntegralFramedTraceCutTask.task_saved P _ hb

private theorem producer_stage (P : Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (ctx aux : List Bool) (j : ℕ) (hj : j ≤ P.cap ctx+1) :
    IntegralMixedHeaderTablesBits.producer P T (keyAt ctx j aux) = lookup (T.commands ctx) j := by
  unfold IntegralMixedHeaderTablesBits.producer
  change lookup (T.commands (pairFst (keyAt ctx j aux))) (prefixLength P (keyAt ctx j aux)) = _
  rw [keyAt_prefix P ctx j aux hj]
  simp only [keyAt, pairFst_pair]

private theorem prelude_header (P : Parameters) (N : List Bool → ℕ) (ctx : List Bool)
    (j : ℕ) (hj : j < N ctx) :
    lookup (IntegralMixedSourceIntegerRecordAppend.headerTable P N ctx) j = zero := by
  let f := fun b => pairFst (IntegralMixedSourceIntegerRecordAppend.headerEntry P N (pair ctx (List.replicate b true)))
  have hi : j < ((List.range (N ctx + IntegralMixedCausalRecordPlanBits.count ctx)).map f).length := by
    simp only [List.length_map, List.length_range]
    omega
  unfold lookup IntegralMixedSourceIntegerRecordAppend.headerTable
  rw [WordList.get_encode, List.getElem?_eq_getElem hi, Option.getD_some]
  simp only [List.getElem_map, List.getElem_range, f,
    IntegralMixedSourceIntegerRecordAppend.headerEntry, pairFst_pair, pairSnd_pair, List.length_replicate,
    ite_eq_left hj, decode_encode]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

/-- Every raw stage uses its actual creating command, rather than the virtual
fallback kind. -/
theorem raw_cut_iff (ctx w : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR false
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) ↔
    IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false := by
  rw [show IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR false =
    IntegralFramedTraceCutScan.StageCut (B).parameters (B).plan from rfl, stage_cut]
  have hs : IntegralMixedVirtualTaskBits.saved (B).parameters
      (IntegralFramedTraceCutTask.task (B).parameters (pair ctx
        (pair (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) true) []))) =
      CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2) :=
    CoefficientMarkedRecordRawCutMetadata.parent_saved hn ht ha hR ctx k hk
  rw [hs]
  have hp : instruction (B).parameters (B).plan
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2)) =
      instruction (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
        (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2)) :=
    IntegralMixedFramedNormalizationBits.planned_instruction
      (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R) (fun _ => 3)
      (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) _
  rw [hp]
  exact CoefficientMarkedRecordTraceStages.raw_cut_iff hn ht ha ctx R k hk _

/-- The literal integer prelude has context-zero producer headers, so no
historical coefficient guard is invoked there. -/
theorem prelude_not_cut (ctx w : List Bool) (j : ℕ)
    (hj : j < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) :
    ¬ IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR false
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) := by
  have hroom := IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  have hcap : j ≤ (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).cap ctx+1 := by omega
  have hcap' : j ≤ (B).parameters.cap ctx+1 := hcap
  rw [show IntegralMixedPhysicalTraceCutScan.StageCut hn ht ha hR false =
    IntegralFramedTraceCutScan.StageCut (B).parameters (B).plan from rfl, stage_cut,
    saved_stage (B).parameters ctx j hcap', isCut_iff_context,
    CoefficientMarkedRecordTraceStages.command_context hn ht ha hR]
  rw [producer_stage _ _ ctx (BinaryNatCode.encode 2) j hcap]
  have hh := prelude_header (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (fun ctx => IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) ctx j hj
  change ¬ 2 ≤ (lookup (IntegralMixedSourceIntegerRecordAppend.headerTable
    (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (fun ctx => IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8) ctx) j).context
  rw [hh]
  decide

end LeanCanny.Encoding.CoefficientMarkedRecordTraceStageBinding

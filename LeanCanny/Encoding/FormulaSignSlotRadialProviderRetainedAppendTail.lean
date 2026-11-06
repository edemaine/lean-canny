/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPlan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordSeedTail
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
/-! # The retained child program has one literal canonical seed completion -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid

noncomputable def meaningfulCodes (old : List Bool) (e : ℕ) :=
  IntegralMixedRoadmapChain.meaningfulCodes (dimension old) (payload (dimension old) old e)

noncomputable def tailCount (old : List Bool) (e : ℕ) :=
  IntegralMixedRoadmapChain.paddingCount (dimension old) (payload (dimension old) old e)+1

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem prepared_seed_records (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) :
    IntegralMixedCausalRecordPlanBits.records (preparedRoot old e)=WordList.encode
      (meaningfulCodes old e++List.replicate (tailCount old e)
        (IntegralMixedChronologicalFrameCode.code ((P).ambient (preparedRoot old e)) [] 0 0)) := by
  have H := IntegralMixedRoadmapChain.raw_seed_tail (checked old hv hd e he)
    (IntegralMixedRoadmapChain.append_seed_probe (dimension old)
      (FormulaSignSlotRadialProviderAtomic.payload old) (endpoint e) (endpoint e) false)
  have HR : IntegralMixedCausalRecordPlanBits.records (preparedRoot old e)=
      IntegralMixedRoadmapChain.raw (payload (dimension old) old e) := by
    unfold preparedRoot
    rw [FormulaSignSlotRadialProviderAtomic.root_records,payload_packet]
  rw [HR]
  simpa only [meaningfulCodes,tailCount,prepared_dimension,IntegralMixedRoadmapChain.seedCode] using H

theorem meaningful_finish (old : List Bool) (e : ℕ) :
    FormulaSignSlotRadialProviderRecordPlan.count (preparedRoot old e)+(meaningfulCodes old e).length=
      finishBirth old e := by
  rw [meaningfulCodes,IntegralMixedRoadmapChain.meaningfulCodes_length,prepared_initial]
  unfold finishBirth FormulaSignSlotRadialProviderAtomic.endBirth IntegralMixedRoadmapAtomic.endBirth
  change N old+IntegralMixedRoadmapChain.rawStart (dimension old) (payload (dimension old) old e)
    (IntegralMixedRoadmapChain.depth (payload (dimension old) old e))=
      N old+IntegralMixedRoadmapChain.rawStart (dimension old)
        (FormulaSignSlotRadialProviderAtomic.payload (packet (dimension old) old e []))
        (depth (packet (dimension old) old e []))
  simp only [FormulaSignSlotRadialProviderAtomic.depth,payload_packet]

theorem full_rules_length (root : List Bool) :
    ((D).rules root).length=FormulaSignSlotRadialProviderRecordPlan.fullCount root := by
  rw [FormulaSignSlotRadialProviderRecordReceipt.rules,IntegralMixedCausalPlanBits.commands_length,
    FormulaSignSlotRadialProviderRecordReceipt.records_length]
  unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
  omega

theorem full_commands (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    (D).rules (preparedRoot old e)=
      List.replicate (tailCount old e) (FormulaSignSlotRadialProviderRecordPlan.seedInstruction (preparedRoot old e))++
        levelProgram old hv hd e he R false := by
  have H := FormulaSignSlotRadialProviderRecordPlan.full_seed_tail (preparedRoot old e) []
    (meaningfulCodes old e) (tailCount old e) (prepared_seed_records old hv hd e he)
  rw [meaningful_finish,local_prefix_commands old hv hd e he R] at H
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend

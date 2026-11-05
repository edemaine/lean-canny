/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordSelectedMetadata
public import LeanCanny.Encoding.CoefficientMarkedRecordRawCutMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuards
/-! # Original-only bounds and selectors in each literal historical cut scan -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceCutMetadata
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem family_choice (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    IntegralMixedRawKindBits.choice (family P D H) key =
      (IntegralMixedCommandHeaderBits.selection (selection P D H key)).choice := by
  change IntegralMixedRawKindBits.choice (family P D H) key =
    IntegralMixedCommandHeaderBits.kindChoice ((family P D H).kind key)
  cases h : (family P D H).kind key <;>
    simp only [IntegralMixedRawKindBits.choice, IntegralMixedCommandHeaderBits.kindChoice, h]

private theorem stage_parent (P : IntegralCriticalHistoryTask.Parameters) (ctx w : List Bool) (j : ℕ) :
    IntegralFramedTraceCutGuards.parent P (IntegralFramedTraceCutScan.stagePacket (pair ctx w) j) =
      IntegralFramedTraceCutTask.task P (pair ctx (pair (List.replicate j true) [])) := by
  simp only [IntegralFramedTraceCutGuards.parent, Function.comp_apply,
    IntegralFramedTraceCutGuards.descriptor, IntegralFramedTraceCutGuards.root,
    IntegralFramedTraceCutScan.stagePacket, pairFst_pair, pairSnd_pair]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def header (ctx : List Bool) (k : ℕ) :=
  IntegralMixedHeaderTablesBits.selected (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
    (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2))

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false

private theorem choice_at_key (key : List Bool) : IntegralMixedRawKindBits.choice (family (B).parameters (B).plan (B).data) key =
    (IntegralMixedHeaderTablesBits.selected (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) key).choice :=
  (family_choice (B).parameters (B).plan (B).data key).trans
    (congrArg IntegralMixedCommandHeaderBits.Header.choice
      (CoefficientMarkedRecordSelectedMetadata.selected_header hn ht ha hR key))

private theorem degree_at_key (key : List Bool) : (family (B).parameters (B).plan (B).data).degree key =
    (IntegralMixedHeaderTablesBits.selected (IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha)
      (CoefficientMarkedRecordCriticalMetadata.tables hn ht ha) key).degree :=
  congrArg IntegralMixedCommandHeaderBits.Header.degree
    (CoefficientMarkedRecordSelectedMetadata.selected_header hn ht ha hR key)

/-- The full word is kept fixed; the stage task has the exact same saved key
as the original canonical raw cut, independent of its sampler ordinal. -/
theorem choice (ctx w : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralFramedTraceCutGuards.choice (B).parameters (B).plan (B).data
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) =
      (header hn ht ha ctx k).choice := by
  unfold IntegralFramedTraceCutGuards.choice
  rw [stage_parent]
  change IntegralMixedRawKindBits.choice (family (B).parameters (B).plan (B).data)
    (IntegralMixedVirtualTaskBits.saved (B).parameters (CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR ctx k)) = _
  have hs : IntegralMixedVirtualTaskBits.saved (B).parameters
      (CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR ctx k) =
      CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2) :=
    CoefficientMarkedRecordRawCutMetadata.parent_saved hn ht ha hR ctx k hk
  rw [hs]
  exact choice_at_key hn ht ha hR _

theorem degree (ctx w : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralFramedTraceCutGuards.degree (B).parameters (B).plan (B).data
      (IntegralFramedTraceCutScan.stagePacket (pair ctx w) (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)) =
      (header hn ht ha ctx k).degree := by
  unfold IntegralFramedTraceCutGuards.degree
  rw [stage_parent]
  change (family (B).parameters (B).plan (B).data).degree
    (IntegralMixedVirtualTaskBits.saved (B).parameters (CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR ctx k)) = _
  have hs : IntegralMixedVirtualTaskBits.saved (B).parameters
      (CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR ctx k) =
      CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2) :=
    CoefficientMarkedRecordRawCutMetadata.parent_saved hn ht ha hR ctx k hk
  rw [hs]
  exact degree_at_key hn ht ha hR _

end LeanCanny.Encoding.CoefficientMarkedRecordTraceCutMetadata

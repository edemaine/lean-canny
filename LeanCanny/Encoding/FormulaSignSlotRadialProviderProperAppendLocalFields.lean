/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendSignatureSyntax
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperOrderComplete
/-! # Constructed endpoint fields imply the actual native strict order -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedChronologicalLevelScalarValues
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  canonicalObservation compiledProgram fullObservation
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd e he
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "q" => packet (dimension old) old R.leftSpec R.rightSpec side
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth

theorem SampledLevel.endpoint_fields (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.bankField (C r) S.receipt.word S.receipt.valid
      (IntegralMixedRoadmapProper.producer false (q S.receipt.word))=left.value V ∧
    FormulaSignSlotRadialProviderAtomic.bankField (C r) S.receipt.word S.receipt.valid
      (IntegralMixedRoadmapProper.producer true (q S.receipt.word))=right.value V := by
  have HL := S.receipt.endpoint_field_at old hv hd left right R side pMID pChild S.local_values R.result.left
  have HR := S.receipt.endpoint_field_at old hv hd left right R side pMID pChild S.local_values R.result.right
  have HP : List.length cs=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  have BL := R.leftLabel.isLt
  have BR := R.rightLabel.isLt
  change IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1<List.length cs+R.result.commands.length at BL
  change IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1<List.length cs+R.result.commands.length at BR
  have EL : beginBirth old+R.result.commands.length-1-R.result.left.val=
      IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1 := by have H := R.left_reference;omega
  have ER : beginBirth old+R.result.commands.length-1-R.result.right.val=
      IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1 := by have H := R.right_reference;omega
  rw [EL] at HL
  rw [ER] at HR
  rw [endpoint_producer_packet old hv hd left right R side false S.receipt.word,
    endpoint_producer_packet old hv hd left right R side true S.receipt.word]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  exact ⟨HL.trans R.result.left_value,HR.trans R.result.right_value⟩

theorem SampledLevel.original_endpoint_fields (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
      (IntegralMixedRoadmapProper.producer false (q S.receipt.word))=left.value V ∧
    FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
      (IntegralMixedRoadmapProper.producer true (q S.receipt.word))=right.value V := by
  simpa only [FormulaSignSlotRadialProviderAtomic.field,context_packet,word_packet] using S.endpoint_fields

theorem SampledLevel.order_bounds (S : SampledLevel old hv hd left right R side pMID pChild) :
    FormulaSignSlotRadialProviderProper.OrderBounds (q S.receipt.word) := by
  have HP : List.length cs=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  have HL := R.leftLabel.isLt
  have HR := R.rightLabel.isLt
  change IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1<List.length cs+R.result.commands.length at HL
  change IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1<List.length cs+R.result.commands.length at HR
  have HC : FormulaSignSlotRadialProviderProper.fullCount (q S.receipt.word)=FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderProper.fullCount
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    simp only [context_packet,FormulaSignSlotRadialProviderRecordPrefix.context,pairFst_pair]
  unfold FormulaSignSlotRadialProviderProper.OrderBounds
  rw [HC,endpoint_producer_packet old hv hd left right R side false S.receipt.word,
    endpoint_producer_packet old hv hd left right R side true S.receipt.word]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  have HF := finish_le_full old hv hd left right R side
  change finishBirth old hv hd left right R side≤FormulaSignSlotRadialProviderRecordPlan.fullCount r at HF
  have HM := midpoint_lt_finish old hv hd left right R side
  unfold midpointBirth at HM
  constructor <;> omega

theorem SampledLevel.original_order (S : SampledLevel old hv hd left right R side pMID pChild)
    (hab : left.value V<right.value V) :
    FormulaSignSlotRadialProviderProper.order (q S.receipt.word)=InfinitesimalSign.encode 1 := by
  apply FormulaSignSlotRadialProviderProper.order_of_fields _ S.atomic_valid S.order_bounds
  rw [S.original_endpoint_fields.1,S.original_endpoint_fields.2]
  exact hab

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

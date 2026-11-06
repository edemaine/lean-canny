/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendLocalFields
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendEndpointWordCutGuard
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperOrderComplete
/-! # Actual frozen fields retain the canonical parent reference values -/
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

local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he

theorem SampledLevel.original_frozen_values (S : SampledLevel old hv hd left right R side pMID pChild)
    (i : Fin (d).labels.length) :
    FormulaSignSlotRadialProviderAtomic.field (q S.receipt.word) S.atomic_valid
      (Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen old) i.val))=V ((d).reference i) := by
  have HL := IntegralMixedChronologicalFrameCode.labels_lookup d i.val i.isLt
  rw [FormulaSignSlotRadialProviderRetainedAppend.parent_labels old hv hd e he] at HL
  have HP : List.length cs=beginBirth old := FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
  have HFit : Nat.fromBitsLE (WordList.get (FormulaSignSlotRadialProviderAtomic.frozen old) i.val)<beginBirth old := by
    rw [HL]
    exact ((d).labels.get i).isLt.trans_eq HP
  have HB : beginBirth old=FormulaSignSlotRadialProviderAtomic.initial old+start old := begin_eq_start old
  have HF := S.accepted_old_fields _ (HFit.trans_eq HB)
  have HV := FormulaSignSlotRadialProviderRetainedAppend.parent_frozen_value old hv hd e he i
  exact HF.trans HV.symm

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

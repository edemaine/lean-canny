/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidSignature
public import LeanCanny.Encoding.IntegralMixedRoadmapMidSignatureLookup
/-! # Both proper sides have identical literal midpoint signatures -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
private theorem plain_payload_eq (q : List Bool) : IntegralMixedRoadmapAtomic.payload q=
    FormulaSignSlotRadialProviderAtomic.payload q := rfl
private theorem plain_depth_eq (q : List Bool) : IntegralMixedRoadmapAtomic.depth q=
    FormulaSignSlotRadialProviderAtomic.depth q := rfl
attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.depth
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentCommands
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : depth old<dimension old) (left right : ParentEndpoint old hv hd)
  (R : CanonicalPair old hv hd left right)
local notation "D" => dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old

private theorem packet_mid_clock (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.midBirth
      (FormulaSignSlotRadialProviderAtomic.dimension (packet D old R.leftSpec R.rightSpec side w))
      (FormulaSignSlotRadialProviderAtomic.initial (packet D old R.leftSpec R.rightSpec side w))
      (packet D old R.leftSpec R.rightSpec side w)=midpointBirth old hv hd left right R:=by
  rw [dimension_packet,initial_packet]
  have HC : IntegralMixedRoadmapProper.midBirth D N (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapProper.midBirth D N (packet D old R.leftSpec R.rightSpec side []) := by
    simp only [IntegralMixedRoadmapProper.midBirth,IntegralMixedRoadmapProper.baseBirth,
      IntegralMixedRoadmapProper.levelIndex,plain_depth_eq,plain_payload_eq,depth_packet,payload_packet]
  exact HC.trans (midpoint_birth old hv hd left right R side)

theorem coarse_labels_packet (side :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.labels (packet D old R.leftSpec R.rightSpec side w)=
      FormulaSignSlotRadialProviderAtomic.frozen old:=by
  simp only [IntegralMixedRoadmapProper.labels,IntegralMixedRoadmapProper.levelIndex,plain_depth_eq,plain_payload_eq,depth_packet,
    Nat.add_sub_cancel,payload_packet,payload]
  exact IntegralMixedRoadmapChain.append_frozen_before D (FormulaSignSlotRadialProviderAtomic.payload old)
    R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
    (FormulaSignSlotRadialProviderAtomic.depth old) (by unfold FormulaSignSlotRadialProviderAtomic.depth;exact le_rfl)

theorem endpoint_producer_packet (side rightSide :Bool) (w :List Bool) :
    IntegralMixedRoadmapProper.producer rightSide (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedRoadmapEndpointSyntax.field (if rightSide then R.rightSpec else R.leftSpec) 1:=by
  have HE:=IntegralMixedRoadmapChain.append_entry_last D (FormulaSignSlotRadialProviderAtomic.payload old)
    R.leftSpec R.rightSpec side (IntegralMixedRoadmapChain.seedCode D)
  cases rightSide <;> simp only [IntegralMixedRoadmapProper.producer,
    IntegralMixedRoadmapProper.levelIndex,plain_depth_eq,plain_payload_eq,depth_packet,Nat.add_sub_cancel,payload_packet,payload,FormulaSignSlotRadialProviderAtomic.depth,
    Bool.false_eq_true,ite_false,ite_true,IntegralMixedRoadmapChain.left,IntegralMixedRoadmapChain.right,
    HE,IntegralMixedRoadmapChain.levelEntry,WordList.get_encode,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]

private theorem packet_signature (side :Bool) (w :List Bool) :
    FormulaSignSlotRadialProviderProperMidSignature.ownSignature
      (packet D old R.leftSpec R.rightSpec side w)=
      IntegralMixedChronologicalPointSignatureCode.code D (midpointBirth old hv hd left right R+1)
        (IntegralMixedChronologicalEndpointCode.appendLabels (FormulaSignSlotRadialProviderAtomic.frozen old)
          (IntegralMixedRoadmapEndpointSyntax.field R.leftSpec 1))++
        pair (BinaryNatCode.encode (IntegralMixedRoadmapEndpointSyntax.field R.rightSpec 1)) []:=by
  unfold FormulaSignSlotRadialProviderProperMidSignature.ownSignature FormulaSignSlotRadialProviderProperMidSignature.signature
    FormulaSignSlotRadialProviderProperMidSignature.extendedLabels IntegralMixedRoadmapProper.midFirst
  rw [packet_mid_clock old hv hd left right R side w,
    coarse_labels_packet old hv hd left right R side w,
    endpoint_producer_packet old hv hd left right R side false w,
    endpoint_producer_packet old hv hd left right R side true w,dimension_packet]
  simp only [Bool.false_eq_true,ite_false,ite_true]

/-- The midpoint signature bytes retain both endpoints and ignore the chosen
child side and the independently sampled full word. -/
theorem midpoint_signature_eq (wL wR :List Bool) :
    FormulaSignSlotRadialProviderProperMidSignature.ownSignature
      (packet D old R.leftSpec R.rightSpec false wL)=
    FormulaSignSlotRadialProviderProperMidSignature.ownSignature
      (packet D old R.leftSpec R.rightSpec true wR):=
  (packet_signature old hv hd left right R false wL).trans
    (packet_signature old hv hd left right R true wR).symm


end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

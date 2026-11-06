/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPrefix
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCanonicalParent
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelRecord
/-! # Actual canonical endpoint pairs bind the general provider append bytes -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old e
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd e he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd e he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd e he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd e he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd e he
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial c
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension old
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial old

noncomputable local instance providerProperCodesIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
noncomputable abbrev ParentEndpoint := Endpoint (cs).length
noncomputable abbrev CanonicalPair (left right : ParentEndpoint old hv hd) :=
  FormulaSignSlotRadialProviderProperParent.Pair old hv hd left right

private theorem canonical_width : (P).width c=FormulaSignSlotRadialProviderAtomic.width old :=
  FormulaSignSlotRadialProviderRetainedAppend.prepared_width old e
private theorem canonical_source_cap : IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient c+1) (Q).degree=
    FormulaSignSlotRadialProviderAtomic.sourceCap old := by
  rw [FormulaSignSlotRadialProviderRecordPlan.spatial_degree,
    FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension]
  change IntegralMixedExceptionalBounds.auxiliaryCap (D+1)
    (FormulaSignSlotRadialProviderRecordPlan.parameters.degree
      (FormulaSignSlotRadialProviderAtomic.root (FormulaSignSlotRadialProviderRetainedAppend.packet D old e [])))=_
  rw [FormulaSignSlotRadialProviderRetainedAppend.degree_provider,
    FormulaSignSlotRadialProviderRetainedAppend.provider_packet]
  unfold FormulaSignSlotRadialProviderAtomic.sourceCap
  rw [FormulaSignSlotRadialProviderRetainedAppend.degree_provider]
private theorem canonical_birth : (cs).length=beginBirth old :=
  FormulaSignSlotRadialProviderRetainedAppend.parent_length old hv hd e he
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.width
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.sourceCap
  FormulaSignSlotRadialProviderAtomic.depth FormulaSignSlotRadialProviderAtomic.frozen
  FormulaSignSlotRadialProviderAtomic.payload FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
variable (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right)

private theorem endpoint_good_transport {n1 n2 B1 B2 C1 C2 m1 m2 u1 u2 :ℕ}
    {labels labels' w :List Bool}
    (H :IntegralMixedRoadmapEndpointSyntax.Good n1 B1 C1 m1 u1 labels w)
    (hn :n1=n2) (hB :B1=B2) (hC :C1=C2) (hm :m1=m2) (hu :u1=u2) (hl :labels=labels'):
    IntegralMixedRoadmapEndpointSyntax.Good n2 B2 C2 m2 u2 labels' w:=by
  cases hn
  cases hB
  cases hC
  cases hm
  cases hu
  cases hl
  exact H

theorem endpoints_good :EndpointsGood old R.leftSpec R.rightSpec:=by
  have HBounds :(d).labels.length+1<(P).ambient c+1:=by
    rw [FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_length,
      FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension]
    omega
  have H:=(R.levelRecord_checked false HBounds).1
  have HL:=H.2.2.1
  have HR:=H.2.2.2.1
  simp only [NativePair.levelRecord,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.left,
    IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair] at HL HR
  have HN:=FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  have HB:=canonical_width old
  have HC:=canonical_source_cap old
  have HM:=canonical_birth old hv hd
  have HLabels:=FormulaSignSlotRadialProviderRetainedAppend.parent_labels old hv hd e he
  exact ⟨endpoint_good_transport HL HN HB HC HM HM HLabels,
    endpoint_good_transport HR HN HB HC HM
      (congrArg (fun m=>m+IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec) HM) HLabels⟩

theorem pair_checked (side : Bool) :
    IntegralMixedRoadmapChain.Checked D (FormulaSignSlotRadialProviderAtomic.width old)
      (FormulaSignSlotRadialProviderAtomic.sourceCap old) N (FormulaSignSlotRadialProviderAtomic.width old)
      (payload D old R.leftSpec R.rightSpec side) :=
  checked old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)

theorem level_codes_compiled (side :Bool):
    (R.levelCodes hk g hg side).reverse=IntegralMixedRoadmapLevel.codes D
      (IntegralMixedRoadmapLevel.packet (FormulaSignSlotRadialProviderAtomic.frozen old) R.leftSpec R.rightSpec side []):=by
  have H:=R.levelCodes_compiled hk g hg
    rfl side
  refine H.trans ?_
  apply congrArg₂ IntegralMixedRoadmapLevel.codes
  · exact FormulaSignSlotRadialProviderRetainedAppend.prepared_dimension old e
  · simp only [NativePair.levelPacket,FormulaSignSlotRadialProviderRetainedAppend.parent_labels]

theorem level_code_count (side :Bool):
    (R.levelCodes hk g hg side).length=IntegralMixedRoadmapEndpointSyntax.fresh R.leftSpec+
      IntegralMixedRoadmapEndpointSyntax.fresh R.rightSpec+2+2*(D-FormulaSignSlotRadialProviderAtomic.depth old):=by
  have H:=congrArg List.length (level_codes_compiled old hv hd left right R side)
  simp only [List.length_reverse,IntegralMixedRoadmapLevel.codes_length,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialProviderAtomic.frozen_count] at H
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

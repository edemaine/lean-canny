/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendWindows
/-! # Native selected coordinates of the proper midpoint and child scalar phases -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "good"=>endpoints_good hn ht ha hR0 old hv hd left right R
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "j"=>start hn ht ha hR0 old
local notation "hj"=>prepared_start_fit hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "newCs"=>parentCommands hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "newX"=>parentState hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "startX"=>IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 r j hj

noncomputable local instance properAppendSelectionIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

attribute [local irreducible] NativePair.orderedFree
  IntegralMixedAuxiliaryMarkedIntegerPlan.spatial IntegralMixedAuxiliaryMarkedIntegerPlan.degree

local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
local notation "sel"=>IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
  (IntegralMixedRoadmapAtomic.context q)
local notation "js"=>R.orderedFree hk

theorem checked_native :IntegralMixedRoadmapChain.Checked
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q) (IntegralMixedRoadmapAtomic.payload q):=by
  rw [dimension_packet,initial_packet,payload_packet]
  simpa only [IntegralMixedRoadmapAtomic.scalarBudget,original_packet] using
    pair_checked hn ht ha hR0 old hv hd left right R side []

private theorem capture_numeric_size :K=D-IntegralMixedRoadmapAtomic.depth old:=by
  have HL:=R.orderedFree_length hk
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  have HLEN:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  have HNUM :((P).ambient c)+1-((d).labels.length+1)=D-IntegralMixedRoadmapAtomic.depth old:=by omega
  exact HL.trans HNUM

theorem midpoint_anchor_selected :sel (finish-1-(K+1+K))= (g).val:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HB :finish-1-(K+1+K)=IntegralMixedRoadmapProper.midBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q:=by omega
  rw [HB]
  have H:=(IntegralMixedRoadmapCheckedProperMetadata.midpoint_anchor hn ht ha hR0 q
    (checked_native hn ht ha hR0 old hv hd left right R side)
    (by rw [depth_packet];omega)).2
  have HG:=IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  unfold IntegralMixedRoadmapProper.levelIndex at H
  rw [depth_packet] at H
  omega

theorem child_anchor_selected :sel (finish-1-K)= (g).val:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HB :finish-1-K=IntegralMixedRoadmapAtomic.anchor
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q:=by omega
  rw [HB]
  have H:=(IntegralMixedRoadmapCheckedProperMetadata.child_anchor hn ht ha hR0 q
    (checked_native hn ht ha hR0 old hv hd left right R side)
    (by rw [depth_packet];omega)).2
  have HG:=IntegralMixedRoadmapProperParent.objective_value hn ht ha hR0 old hv hd
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  rw [depth_packet] at H
  omega

theorem midpoint_capture_selected (k :Fin K):sel (finish-1-(K+1+k.val)) =IntegralMixedRoadmapAtomic.depth old+1+k.val:=by
  let i:=K-1-k.val
  have HK:=capture_count hn ht ha hR0 old hv hd left right R side
  have HI :i<IntegralMixedRoadmapProper.captureCount (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q:=by
    dsimp only [i];have :=k.isLt;omega
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HB :finish-1-(K+1+k.val)=IntegralMixedRoadmapProper.midFirst
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i:=by
    unfold IntegralMixedRoadmapProper.midFirst
    dsimp only [i];have :=k.isLt;omega
  rw [HB]
  have H:=(IntegralMixedRoadmapCheckedProperMetadata.midpoint_capture hn ht ha hR0 q
    (checked_native hn ht ha hR0 old hv hd left right R side)
    (by rw [depth_packet];omega) i HI).2
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  have HLEN:=capture_numeric_size hn ht ha hR0 old hv hd left right R
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  have HR :IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q-i=IntegralMixedRoadmapAtomic.depth old+1+k.val:=by
    rw [dimension_packet]
    dsimp only [i]
    have :=k.isLt
    omega
  exact H.trans HR

theorem child_capture_selected (k :Fin K):sel (finish-1-k.val) =IntegralMixedRoadmapAtomic.depth old+1+k.val:=by
  let i:=K-1-k.val
  have HK:=child_free hn ht ha hR0 old hv hd left right R side
  have HI :i<IntegralMixedRoadmapAtomic.free (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q) q:=by
    dsimp only [i];have :=k.isLt;omega
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HB :finish-1-k.val=IntegralMixedRoadmapAtomic.first
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q+i:=by
    unfold IntegralMixedRoadmapAtomic.first
    dsimp only [i];have :=k.isLt;omega
  rw [HB]
  have H:=(IntegralMixedRoadmapCheckedProperMetadata.child_capture hn ht ha hR0 q
    (checked_native hn ht ha hR0 old hv hd left right R side) i HI).2
  have HL:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he
  have HLEN:=capture_numeric_size hn ht ha hR0 old hv hd left right R
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e
  have HR :IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q-i=IntegralMixedRoadmapAtomic.depth old+1+k.val:=by
    rw [dimension_packet]
    dsimp only [i]
    have :=k.isLt
    omega
  exact H.trans HR

private theorem ordered_coordinate (k :Fin K):
    ((js).get k).val.val=IntegralMixedRoadmapAtomic.depth old+1+k.val:=by
  exact (R.orderedFree_get hk k).trans (by
    rw [IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd e he])

theorem midpoint_capture_selected_ordered (k :Fin K):
    sel (finish-1-(K+1+k.val))=((js).get k).val.val:=
  (midpoint_capture_selected hn ht ha hR0 old hv hd left right R side k).trans
    (ordered_coordinate hn ht ha hR0 old hv hd left right R k).symm

theorem child_capture_selected_ordered (k :Fin K):
    sel (finish-1-k.val)=((js).get k).val.val:=
  (child_capture_selected hn ht ha hR0 old hv hd left right R side k).trans
    (ordered_coordinate hn ht ha hR0 old hv hd left right R k).symm

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

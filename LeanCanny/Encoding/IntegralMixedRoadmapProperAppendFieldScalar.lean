/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendLevelFields
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendSelectionReadback
/-! # Actual scalar equality throughout the proper midpoint and child phases -/
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

noncomputable local instance properAppendFieldScalarIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

local notation "m"=>List.length oldCs+List.length R.result.commands
local notation "js"=>R.orderedFree hk
local notation "C"=>canonicalObservation hn ht ha hR0 old hv hd left right R side
local notation "localCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "finish"=>finishBirth hn ht ha hR0 old hv hd left right R side
local notation "SAMP"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
open IntegralMixedChronologicalLevelScalarValues

local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
local notation "anchor"=>IntegralMixedRoadmapAtomic.anchor
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
local notation "sel"=>IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
  (IntegralMixedRoadmapAtomic.context q)

private theorem extend_at {a :ℕ} (p :Fin a→ℝ) (i :Fin a) (coord :ℕ) (hcoord :coord=i.val):
    IntegralMixedFramedBankObservation.extend p coord=p i:=by
  subst coord
  unfold IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left i.isLt]

theorem WordReceipt.scalar_before_finish {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finish):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid b=
      IntegralMixedFramedBankObservation.extend (if b<anchor then pMID else pChild) (sel b):=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HA:=child_anchor hn ht ha hR0 old hv hd left right R side
  by_cases hMid :b<anchor
  · rw [ite_eq_left hMid]
    by_cases hAnchor :b=mid
    · have HB :finish-1-(K+1+K)=b:=by omega
      have HV:=W.midpoint_anchor_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
      have HS:=midpoint_anchor_selected hn ht ha hR0 old hv hd left right R side
      rw [HB] at HV HS
      exact HV.trans (extend_at pMID g (sel b) HS).symm
    · let k :Fin K:=⟨mid+K-b,by omega⟩
      have HB :finish-1-(K+1+k.val)=b:=by dsimp only [k];omega
      have HV:=W.midpoint_capture_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues k
      have HS:=midpoint_capture_selected_ordered hn ht ha hR0 old hv hd left right R side k
      rw [HB] at HV HS
      exact HV.trans (extend_at pMID ((js).get k).val (sel b) HS).symm
  · rw [ite_eq_right hMid]
    by_cases hAnchor :b=anchor
    · have HB :finish-1-K=b:=by omega
      have HV:=W.child_anchor_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
      have HS:=child_anchor_selected hn ht ha hR0 old hv hd left right R side
      rw [HB] at HV HS
      exact HV.trans (extend_at pChild g (sel b) HS).symm
    · let k :Fin K:=⟨finish-1-b,by omega⟩
      have HB :finish-1-k.val=b:=by dsimp only [k];omega
      have HV:=W.child_capture_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues k
      have HS:=child_capture_selected_ordered hn ht ha hR0 old hv hd left right R side k
      rw [HB] at HV HS
      exact HV.trans (extend_at pChild ((js).get k).val (sel b) HS).symm

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

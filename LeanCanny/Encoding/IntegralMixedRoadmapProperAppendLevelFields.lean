/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendFieldReadback
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelScalarValues
/-! # Scalar capture phases of a sampled canonical proper append -/
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

noncomputable local instance properAppendLevelFieldsIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

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

private theorem level_scalar_length :(localCs).length=m+1+K+1+K:=by
  rw [compiled_program_length hn ht ha hR0 old hv hd left right R side]
  unfold finishBirth
  rw [R.levelCodes_length]
  have HP:=IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  change (oldCs).length=beginBirth hn ht ha hR0 old at HP
  omega

theorem WordReceipt.level_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i)
    (i :Fin (m+1+K+1+K)):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-i.val)=levelValues pMID pChild R.result.nextValues g js i:=by
  have HL:=level_scalar_length hn ht ha hR0 old hv hd left right R side
  have HF:=compiled_program_length hn ht ha hR0 old hv hd left right R side
  have HH:=W.local_field hn ht ha hR0 old hv hd left right R side (finish-1-i.val) (by have :=i.isLt;omega)
  have HE :(localCs).length-1-(finish-1-i.val)=i.val:=by have :=i.isLt;omega
  rw [HE] at HH
  exact HH.trans (hValues i)

theorem WordReceipt.child_capture_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i) (k :Fin K):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-(k.val))=pChild ((js).get k).val:=by
  exact (W.level_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    ⟨k.val,by have :=k.isLt;omega⟩).trans (child_capture pMID pChild R.result.nextValues g js k)

theorem WordReceipt.child_anchor_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-(K))=pChild g:=by
  exact (W.level_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    ⟨K,by omega⟩).trans (IntegralMixedChronologicalLevelScalarValues.child_anchor pMID pChild R.result.nextValues g js)

theorem WordReceipt.midpoint_capture_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i) (k :Fin K):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-(K+1+k.val))=pMID ((js).get k).val:=by
  exact (W.level_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    ⟨K+1+k.val,by have :=k.isLt;omega⟩).trans (midpoint_capture pMID pChild R.result.nextValues g js k)

theorem WordReceipt.midpoint_anchor_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-(K+1+K))=pMID g:=by
  exact (W.level_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    ⟨K+1+K,by omega⟩).trans (midpoint_anchor pMID pChild R.result.nextValues g js)

theorem WordReceipt.endpoint_field {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (pMID pChild :Fin ((P).ambient c+1)→ℝ)
    (hValues :∀i :Fin (m+1+K+1+K),(C).point z i.val=levelValues pMID pChild R.result.nextValues g js i) (k :Fin m):
    IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (pair r []) W.word W.valid
      (finish-1-(K+1+(K+1+k.val)))=R.result.nextValues k:=by
  exact (W.level_field hn ht ha hR0 old hv hd left right R side pMID pChild hValues
    ⟨K+1+(K+1+k.val),by have :=k.isLt;omega⟩).trans (endpoint_value pMID pChild R.result.nextValues g js k)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

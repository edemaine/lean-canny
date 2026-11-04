/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParentMetadata
public import LeanCanny.Encoding.IntegralMixedMarkedReservedSelectionReceipt
/-! # Pure reserved-probe task readback precedes sampling and factor guards -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTask
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "wid"=>IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0)
variable (z : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))

include hh in
theorem stage_cap :creating (ini z) (pairFst z)≤(P).cap (preparedRoot (dim z) z)+1:=by
 change creating (ini z) (pairFst z)≤number n (preparedRoot (dim z) z)+8+
   IntegralMixedCausalRecordPlanBits.count (preparedRoot (dim z) z)+2+1
 rw [prepared_count _ z hh.1,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 unfold creating
 rw [HI]
 omega

include hh in
theorem saved :old=keyAt (preparedRoot (dim z) z) (creating (ini z) (pairFst z)) (BinaryNatCode.encode 2):=by
 have HC :IntegralFramedTraceCutTask.stage (pair (pairFst (ctx z)) (pair (IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)) []))≤
     birthCap P (pairFst (pair (pairFst (ctx z)) (pair (IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)) []))):=by
   simp only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair,
     IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z,
     IntegralMixedRoadmapBadProbeProvenance.context_birth hn ht ha hR0 z,birthCap]
   exact stage_cap hn ht ha hR0 z hh
 simpa only [IntegralMixedPhysicalCutOpenInterval.parent,pairFst_pair,IntegralFramedTraceCutTask.stage_packet,
   IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z,
   IntegralMixedRoadmapBadProbeProvenance.context_birth hn ht ha hR0 z] using
   IntegralFramedTraceCutTask.task_saved P (pair (pairFst (ctx z)) (pair (IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)) [])) HC

include hh in
theorem parent_time :creating (ini z) (pairFst z)=number n (preparedRoot (dim z) z)+8+
    (IntegralMixedCausalRecordPlanBits.count (preparedRoot (dim z) z)-1):=by
 rw [prepared_count _ z hh.1,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 unfold creating
 rw [HI]
 have HC:=hh.1
 omega

include hh in
theorem snapshot :IntegralMixedPrefixSnapshot.ofState ((G).state old)=
    IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (preparedRoot (dim z) z):=by
 have HE:=congrArg (fun key=>IntegralMixedPrefixSnapshot.ofState ((G).state key)) (saved hn ht ha hR0 z hh)
 rw [parent_time hn ht ha hR0 z hh] at HE
 have HF:=IntegralMixedMarkedPrefixSnapshot.family_keyAt hn ht ha hR0 (preparedRoot (dim z) z)
   (IntegralMixedCausalRecordPlanBits.count (preparedRoot (dim z) z)-1) (Nat.sub_le _ _) (BinaryNatCode.encode 2)
 exact HE.trans HF

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTask

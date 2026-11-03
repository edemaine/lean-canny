/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowReadback
public import LeanCanny.Encoding.IntegralMixedMarkedReservedRuling

/-! # The reserved row query names its literal, unclipped creating prefix -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family prefixLength)
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank dimension initial creating

noncomputable def parentKey (mean : Bool) (z : List Bool):=
  IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR0 mean z)

theorem root_number (mean : Bool) (z : List Bool) :
    number n (root hn ht ha hR0 mean z)+8=initial hn ht ha hR0 z :=by
  rw [initial,IntegralMixedRoadmapAtomic.initial_eq hn ht ha hR0]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,
    IntegralMixedRoadmapAtomic.original,atomic]

theorem root_dimension (mean : Bool) (z : List Bool) :
    (P).ambient (root hn ht ha hR0 mean z)=dimension hn ht ha hR0 z :=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  change number n (root hn ht ha hR0 mean z)+3=_
  rw [dimension,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,pairFst_pair,
    IntegralMixedRoadmapAtomic.original,atomic]

theorem creating_bound (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    creating hn ht ha hR0 z≤birthCap P (root hn ht ha hR0 mean z) :=by
  unfold IntegralMixedPhysicalMarkedPlan.bank
  change creating hn ht ha hR0 z≤number n (root hn ht ha hR0 mean z)+8+
    IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR0 mean z)+2+1
  rw [root_number hn ht ha hR0,root_count hn ht ha hR0 mean z hc]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating
  omega

theorem parent_root (mean : Bool) (z : List Bool) :
    RankedHistoryTask.root (parent hn ht ha hR0 mean z)=root hn ht ha hR0 mean z :=by
  rw [parent,IntegralMixedRoutineContextQuery.query_root]
  exact RankedHistoryTask.root_pack _ _ _ _

theorem parent_birth (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    birth P (parent hn ht ha hR0 mean z)=creating hn ht ha hR0 z :=by
  apply IntegralMixedRoutineContextQuery.query_birth
  rw [base,RankedHistoryTask.root_pack]
  exact creating_bound hn ht ha hR0 mean z hc

theorem parentKey_root (mean : Bool) (z : List Bool) :
    pairFst (parentKey hn ht ha hR0 mean z)=root hn ht ha hR0 mean z :=by
  simp only [parentKey,IntegralMixedVirtualTaskBits.saved,pairFst_pair,parent_root]

theorem parentKey_prefix (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    prefixLength P (parentKey hn ht ha hR0 mean z)=creating hn ht ha hR0 z :=by
  change prefixLength P (IntegralMixedFramedHistoryFamilyBits.keyAt _ _ _)=_
  rw [IntegralMixedFramedHistoryFamilyBits.keyAt_prefix]
  · exact parent_birth hn ht ha hR0 mean z hc
  · rw [parent_root,parent_birth hn ht ha hR0 mean z hc]
    exact creating_bound hn ht ha hR0 mean z hc

theorem parentKey_records (mean : Bool) (z : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (pairFst (parentKey hn ht ha hR0 mean z))=
      WordList.encode (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)++[code hn ht ha hR0 mean z]) :=by
  rw [parentKey_root]
  simp only [IntegralMixedCausalRecordPlanBits.records,root,pairFst_pair,pairSnd_pair,raw]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

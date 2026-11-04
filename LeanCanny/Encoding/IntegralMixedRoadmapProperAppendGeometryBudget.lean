/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendCodes
public import LeanCanny.Encoding.IntegralMixedRoadmapChainRoom
/-! # The fixed original program budget pays for an arbitrary proper level -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

/-- Enough room for two fresh endpoints, two anchors, and both free-coordinate
capture blocks, before any endpoint pair or native word has been chosen. -/
theorem level_raw_room (a0 :ℕ) (payload :List Bool) (idx :ℕ) (hi :idx≤a0):
    IntegralMixedRoadmapChain.rawStart a0 payload idx+4+2*(a0-idx)≤
      IntegralMixedRoadmapRecordChain.recordBound a0:=by
  have H:=IntegralMixedRoadmapChain.prefixCount_bound a0 payload idx (by omega)
  have H1 :a0+1-idx=a0-idx+1:=by omega
  have H4 :a0+4-idx=a0-idx+4:=by omega
  have HR :4+2*(a0-idx)≤(a0+1-idx)*(a0+4-idx):=by
    rw [H1,H4]
    nlinarith
  unfold IntegralMixedRoadmapChain.rawStart IntegralMixedRoadmapRecordChain.recordBound
  omega

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapRetainedAppend.parentCommands
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus

/-- The actual canonical parent has the full geometric level horizon using
only the accepted old history and its original fixed record budget. -/
theorem canonical_level_horizon :
    (cs).length+4+2*((P).ambient c-(d).labels.length)≤(P).cap c+2:=by
  have HC:=IntegralMixedRoadmapAtomic.checked hn ht ha hR0 old hv
  have HOldCount :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old)=
      IntegralMixedRoadmapRecordChain.probedRecordBound D:=by
    simpa only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
      IntegralMixedRoadmapAtomic.root,pairFst_pair,pairSnd_pair] using HC.2.2.2.2.2.2.1
  have HCount :IntegralMixedCausalRecordPlanBits.count c=IntegralMixedRoadmapRecordChain.probedRecordBound D:=
    (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd E he).trans HOldCount
  have HCap :(P).cap c=number n c+8+IntegralMixedCausalRecordPlanBits.count c+2:=rfl
  have HI:=IntegralMixedRoadmapRetainedAppend.initial_root hn ht ha hR0 old E
  have HBound:=level_raw_room D (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old) hd.le
  have HM :(cs).length=I+IntegralMixedRoadmapChain.rawStart D
      (IntegralMixedRoadmapAtomic.payload old) (IntegralMixedRoadmapAtomic.depth old):=by
    simpa only [IntegralMixedRoadmapAtomic.endBirth] using
      IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd E he
  have HDIM:=IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old E
  have HDESC:=IntegralMixedRoadmapRetainedAppend.parent_descriptor_length hn ht ha hR0 old hv hd E he
  have HL :(cs).length+4+2*((P).ambient c-(d).labels.length)=
      I+IntegralMixedRoadmapChain.rawStart D (IntegralMixedRoadmapAtomic.payload old)
        (IntegralMixedRoadmapAtomic.depth old)+4+2*(D-IntegralMixedRoadmapAtomic.depth old):=
    congrArg₂ (fun len rest=>len+4+2*rest) HM (congrArg₂ (fun dim dep=>dim-dep) HDIM HDESC)
  rw [HL]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound at HCount
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

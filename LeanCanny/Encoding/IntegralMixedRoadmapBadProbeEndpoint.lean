/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutEndpointField
/-! # Actual reserved endpoints are old parent values from the same full word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeEndpoint
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket IntegralMixedPhysicalCutOpenInterval
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "wid"=>IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0)
variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w)
 (hb : Bounds hn ht ha (radius_binary hR0) false (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))

theorem selected_index (side : Bool) :selected side (ctx z)=creating (ini z) (pairFst z)-producer side (pairFst z):=by
 cases side <;> simp only [selected,IntegralMixedRoadmapBadProbeTest.intervalContext,intervalContext,
   pairSnd_pair,pairFst_pair,Bool.false_eq_true,ite_false,ite_true,BinaryNatCode.encode,Nat.fromBitsLE_bits]

include hh in
theorem producer_bound (side : Bool) :producer side (pairFst z)<creating (ini z) (pairFst z):=by
 rcases hh with ⟨_,_,_,_,_,_,_,hl,hr⟩
 cases side
 · exact hl
 · exact hr

include hh in
theorem parent_count :IntegralMixedMarkedPrefixFieldReadback.parent n (pairFst (ctx z))=creating (ini z) (pairFst z):=by
 rw [IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z]
 unfold IntegralMixedMarkedPrefixFieldReadback.parent
 rw [prepared_count _ z hh.1,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=
   IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 unfold creating
 rw [HI]

include hh in
theorem endpoint_parent (side : Bool)
    (hi : selected side (ctx z)<count hn ht ha (radius_binary hR0) false (ctx z)) :
    IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false side (ctx z) w hv hi=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
        (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv)
        (creating (ini z) (pairFst z)-1-producer side (pairFst z)):=by
 have HP:=producer_bound hn ht ha hR0 z hh side
 have HC :0<IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z)):=by
   rw [IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z,prepared_count _ z hh.1]
   exact hh.1
 have HI :creating (ini z) (pairFst z)-1-producer side (pairFst z)<
     IntegralMixedMarkedPrefixFieldReadback.parent n (pairFst (ctx z)):=by
   rw [parent_count hn ht ha hR0 z hh]
   omega
 have HV:=IntegralMixedMarkedPrefixFieldReadback.parent_value hn ht ha hR0 (pairFst (ctx z)) w
   (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv) HC _ HI
 have HJ :creating (ini z) (pairFst z)-1-producer side (pairFst z)+1=selected side (ctx z):=by
   rw [selected_index hn ht ha hR0 z side]
   omega
 rw [HJ] at HV
 exact (IntegralMixedPhysicalCutEndpointField.endpoint_field hn ht ha hR0 (ctx z) w hv side hi).trans
   ((IntegralMixedPhysicalMarkedContext.pointNewest_eq hn ht ha (radius_binary hR0) (ctx z)
     (IntegralMixedMarkedPrefixFieldReadback.context (pairFst (ctx z))) w (pairFst_pair _ _).symm hv
     (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv) _).trans HV.symm)

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeEndpoint

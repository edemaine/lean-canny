/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePresence
/-! # Native probe witnesses are actual ordinary bad heights of the base parent

The original full word and the prepared full word are independent valid
words. Their native field scan identifies every old quotient, not root
ordinals, raw coordinates, or independently selected interpretations.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralFramedPhysicalSquare.input
 IntegralFramedPhysicalSquare.point IntegralMixedRoadmapBadProbeParent.snapshot
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "EP"=>IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false

noncomputable def endpoint (q : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context (root q)) (word q))
    (side : Bool):ℝ:=IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root q) (word q) hv
      (creating ((B).parameters.ambient (root q)+5) q-1-producer side q)

variable (z w : List Bool)
 (hl : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
 (hw : IntegralMixedRoadmapBadProbeTest.Witness hn ht ha (radius_binary hR0) (pair z w))

include hw in
theorem hint :HintGood (dim z) (ini z) (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z:=by
 simpa only [pairFst_pair] using hw.1

include hw in
theorem full_valid :SquareSampleCompleteVertices.Valid S (ctx z) w:=by
 simpa only [pairFst_pair,pairSnd_pair] using hw.2.2.1

include hw in
theorem bounds :IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false (pair (ctx z) w):=by
 simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using hw.2.2.2.1

include hw in
theorem fields :IntegralMixedRoadmapBadProbeFields.packet (dim z) (ini z) z w∈
    IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0):=by
 simpa only [IntegralMixedRoadmapBadProbeTest.fieldPacket,pairFst_pair,pairSnd_pair,
   IntegralMixedRoadmapBadProbeFields.packet,IntegralMixedRoadmapBadProbeFields.leftContext,
   IntegralMixedRoadmapBadProbeFields.rightContext] using hw.2.1

include hw in
theorem parent_fields :∀i<creating (ini z) (pairFst z),
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) hl i=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (preparedRoot (dim z) z) w
        (IntegralMixedRoadmapBadProbePresence.prepared_valid hn ht ha hR0 z w (full_valid hn ht ha hR0 z w hw)) i:=
 (IntegralMixedMarkedPrefixFieldReadback.packet_parent_iff hn ht ha hR0 (dim z) (ini z) z w
   (hint hn ht ha hR0 z w hw).1 rfl hl _).mp (fields hn ht ha hR0 z w hw)

include hw in
theorem selected_bound (side : Bool) :IntegralMixedPhysicalCutOpenInterval.selected side (ctx z)<
    IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (ctx z):=by
 cases side
 · exact IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w
     (bounds hn ht ha hR0 z w hw)
 · exact IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w
     (bounds hn ht ha hR0 z w hw)

include hw in
theorem endpoint_eq (side : Bool) :
    EP side (ctx z) w (full_valid hn ht ha hR0 z w hw)
      (selected_bound hn ht ha hR0 z w hw side)=
      endpoint hn ht ha hR0 (pairFst z) hl side:=by
 have HH:=hint hn ht ha hR0 z w hw
 have HP:=IntegralMixedRoadmapBadProbeEndpoint.producer_bound hn ht ha hR0 z HH side
 have HI :creating (ini z) (pairFst z)-1-producer side (pairFst z)<creating (ini z) (pairFst z):=by omega
 have HE:=IntegralMixedRoadmapBadProbeEndpoint.endpoint_parent hn ht ha hR0 z w HH
   (full_valid hn ht ha hR0 z w hw) side (selected_bound hn ht ha hR0 z w hw side)
 have HC:=congrFun (IntegralMixedRoadmapBadProbePresence.parent_values hn ht ha hR0 z w
   (full_valid hn ht ha hR0 z w hw)) (creating (ini z) (pairFst z)-1-producer side (pairFst z))
 exact HE.trans (HC.trans (parent_fields hn ht ha hR0 z w hl hw _ HI).symm)

include hw in
theorem ordinary_bad
    (hab :endpoint hn ht ha hR0 (pairFst z) hl false<endpoint hn ht ha hR0 (pairFst z) hl true) :
    ∃u∈Set.Ioo (endpoint hn ht ha hR0 (pairFst z) hl false) (endpoint hn ht ha hR0 (pairFst z) hl true),
      u∈IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) (labels (pairFst z)) hl:=by
 have HV:=full_valid hn ht ha hR0 z w hw
 have HB:=bounds hn ht ha hR0 z w hw
 have HH:=hint hn ht ha hR0 z w hw
 have HG :IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha (radius_binary hR0) false (pair (ctx z) w):=by
   simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using hw.2.2.2.2.1
 have HN :pair (ctx z) w∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha (radius_binary hR0) false:=by
   simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using hw.2.2.2.2.2
 have HO :EP false (ctx z) w HV (IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w HB)<
     EP true (ctx z) w HV (IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w HB):=by
   rw [endpoint_eq hn ht ha hR0 z w hl hw false,endpoint_eq hn ht ha hR0 z w hl hw true]
   exact hab
 obtain ⟨u,hu,hbad⟩:=IntegralMixedRoadmapBadProbePresence.present_prepared hn ht ha hR0 z w HH HV HB HG HO HN
 have HE:=IntegralMixedRoadmapBadProbeParent.bad_eq_of_fields hn ht ha hR0 (dim z) (ini z) z w HH.1 rfl hl
   (IntegralMixedRoadmapBadProbePresence.prepared_valid hn ht ha hR0 z w HV) (fields hn ht ha hR0 z w hw)
 refine ⟨u,?_,(congrArg (fun A : Set ℝ=>u∈A) HE.symm).mp hbad⟩
 simpa only [endpoint_eq hn ht ha hR0 z w hl hw false,endpoint_eq hn ht ha hR0 z w hl hw true] using hu

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound

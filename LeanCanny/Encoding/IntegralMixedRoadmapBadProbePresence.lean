/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutOrdinaryPresence
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeEndpoint
/-! # Native negative ordinary probes refer to their actual quotient-determined parent -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbePresence
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralFramedPhysicalSquare.input
 IntegralFramedPhysicalSquare.point IntegralMixedRoadmapBadProbeParent.snapshot
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "EP"=>IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false
variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w)
 (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false
   (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))
local notation "hl"=>IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w hb
local notation "hr"=>IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w hb

include hv in
theorem prepared_valid :SquareSampleCompleteVertices.Valid S
    (IntegralMixedMarkedPrefixFieldReadback.context (preparedRoot (dim z) z)) w:=
 (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha (radius_binary hR0) (ctx z)
   (IntegralMixedMarkedPrefixFieldReadback.context (preparedRoot (dim z) z)) w
   ((IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z).trans (pairFst_pair _ _).symm)).mp hv

private theorem point_congr (a b : List Bool) (h : a=b) (v : List Bool)
    (hla : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context a) v)
    (hlb : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context b) v) :
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 a v hla=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 b v hlb:=by
 cases h
 rfl

include hv in
theorem parent_values :IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
    (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv)=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (preparedRoot (dim z) z) w
        (prepared_valid hn ht ha hR0 z w hv):=
 point_congr hn ht ha hR0 _ _ (IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z) w _ _

include hh in
theorem present_prepared
    (hg : IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha (radius_binary hR0) false (pair (ctx z) w))
    (hab : EP false (ctx z) w hv hl<EP true (ctx z) w hv hr)
    (hno :pair (ctx z) w∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha (radius_binary hR0) false) :
    ∃u∈Set.Ioo (EP false (ctx z) w hv hl) (EP true (ctx z) w hv hr),
      u∈IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0 (preparedRoot (dim z) z) w (labels (pairFst z))
        (prepared_valid hn ht ha hR0 z w hv):=by
 obtain ⟨u,hu,hbad⟩:=IntegralMixedPhysicalCutOrdinaryPresence.present hn ht ha hR0 z w hh hv hb hg hab hno
 have HE:=congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>d.bad (labels (pairFst z))
   (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
     (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv)))
   (IntegralMixedRoadmapBadProbeParent.saved_snapshot hn ht ha hR0 z w hh hb)
 have HV:=congrArg (fun values=>(IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (preparedRoot (dim z) z)).bad
   (labels (pairFst z)) values) (parent_values hn ht ha hR0 z w hv)
 exact ⟨u,hu,(congrArg (fun A : Set ℝ=>u∈A) (HE.trans HV)).mp hbad⟩

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbePresence

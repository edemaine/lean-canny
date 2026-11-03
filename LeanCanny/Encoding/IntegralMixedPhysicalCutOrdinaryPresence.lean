/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
public import LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotRawBad
/-! # A native negative ordinary probe exhibits a bad height of its actual parent -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutOrdinaryPresence
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
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
local notation "EP"=>IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
 IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point
 IntegralMixedPhysicalCutOpenInterval.parent IntegralMixedVirtualTaskBits.saved

variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w)
 (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false
   (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))
local notation "hl"=>IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w hb
local notation "hr"=>IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w hb

include hh in
theorem present
    (hg : IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha (radius_binary hR0) false (pair (ctx z) w))
    (hab : EP false (ctx z) w hv hl<EP true (ctx z) w hv hr)
    (hno :pair (ctx z) w∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha (radius_binary hR0) false) :
    ∃u∈Set.Ioo (EP false (ctx z) w hv hl) (EP true (ctx z) w hv hr),
      u∈(IntegralMixedPrefixSnapshot.ofState ((G).state old)).bad (labels (pairFst z))
        (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
          (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w hv)):=by
 obtain ⟨φ,hφ,HV,_,HI⟩:=IntegralMixedPhysicalCutCoefficientPresence.interpreted_present_iff
   hn ht ha (radius_binary hR0) false (ctx z) w hv hb hg hab
 obtain ⟨u,hu,hroot⟩:=HI.mp hno
 have HC :0<IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z)):=by
   rw [IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z,prepared_count _ z hh.1]
   exact hh.1
 have HQ:=IntegralMixedPhysicalCutParentPoint.quotients hn ht ha hR0 (ctx z) w hv hb HC
   (IntegralMixedRoadmapBadProbeProvenance.last_birth hn ht ha hR0 z hh) φ hφ
 obtain ⟨hg',HR⟩:=IntegralMixedRoadmapBadProbeProvenance.rule_raw hn ht ha hR0 z w hh hb
 have HF:=IntegralMixedPrefixSnapshot.ofState_mem_bad_iff ((G).state old) ((G).birth_bound old)
   (family_canonical P D H old) (labels (pairFst z)) (Nat.fromBitsLE (field 1 z)) hg' φ _ HQ u
 change (G).rule old=(IntegralMixedChronologicalCutCode.rawData ((G).ambient old) ((G).birth old)
   (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)) hg').rule
     (commonDenominator ((G).state old)) (commonDenominator_ne_zero ((G).state old)) at HR
 rw [←HR] at HF
 exact ⟨u,hu,HF.mpr ⟨(G).kind old,HV,
   IntegralMixedRoadmapBadProbeProvenance.ordinary hn ht ha hR0 z w hh hb,hroot⟩⟩

end LeanCanny.Encoding.IntegralMixedPhysicalCutOrdinaryPresence

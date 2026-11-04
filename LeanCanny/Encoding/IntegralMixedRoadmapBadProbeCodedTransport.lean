/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRuntime
public import LeanCanny.Encoding.IntegralMixedPhysicalCutParentPoint
/-! # The same chosen byte witness survives actual all-old-field matching -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCodedTransport
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits IntegralMixedRoadmapBadProbePacket
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
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hl :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
 (hr :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedMarkedPrefixFieldReadback.context (preparedRoot (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z) z)) w)
local notation "VL"=>IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) hl
local notation "VR"=>IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (preparedRoot (dim z) z) w hr
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))

include hh in
theorem actual (a : ℝ)
    (hf :∀i<creating (ini z) (pairFst z),VL i=VR i)
    (hcoded : (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).CodedFactor
      (labels (pairFst z)) VL a (probe (dim z) z)) :
    (IntegralMixedPrefixSnapshot.ofState ((G).state old)).CodedFactor (labels (pairFst z)) VR a (probe (dim z) z):=by
 have HB:=IntegralMixedRoadmapBadProbeParent.packet_birth hn ht ha hR0 (pairFst z) hh.1
 have HP:=IntegralMixedRoadmapBadProbeParent.snapshot_prepared hn ht ha hR0 (dim z) z hh.1
 have HC:=(IntegralMixedPrefixSnapshot.Data.coded_transport _ _ HP (labels (pairFst z)) VL VR a (probe (dim z) z)
   (fun i hi=>hf i (hi.trans_eq HB))).mp hcoded
 exact (congrArg (fun A :IntegralMixedPrefixSnapshot.Data=>A.CodedFactor (labels (pairFst z)) VR a (probe (dim z) z))
   (IntegralMixedRoadmapBadProbeTask.snapshot hn ht ha hR0 z hh)).mpr HC

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCodedTransport

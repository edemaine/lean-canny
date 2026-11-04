/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointCaptures
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowParent
public import LeanCanny.Encoding.IntegralMixedRoadmapChainRoom
/-! # Actual MID and child producers precede the reserved row probe -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial

theorem creating_eq (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) (j : ℕ) :
    IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (pair q (BinaryNatCode.encode j))=
      N q+IntegralMixedRoadmapRecordChain.recordBound (D q) :=by
  have HR:=IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 q hv
  unfold IntegralMixedRoadmapProperRow.creating IntegralMixedRoadmapBadProbePacket.creating
  simp only [IntegralMixedRoadmapProperRow.initial,IntegralMixedRoadmapProperRow.atomic,
    IntegralMixedRoadmapProperRow.oldPacket,badPacket,IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  rw [HR]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem child_producer_before_probe (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (j : ℕ) (hj : IntegralMixedRoadmapAtomic.depth q ≤ j) (hjn : j ≤ D q) :
    childProducer (D q) (N q) q j < IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (pair q (BinaryNatCode.encode j)) :=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HE:=IntegralMixedRoadmapAtomic.latest_block_end hn ht ha hR0 q hv
  have HB:=IntegralMixedRoadmapChain.rawStart_bound (D q) (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapAtomic.depth q) (by omega)
  rw [creating_eq hn ht ha hR0 q hv j]
  unfold childProducer IntegralMixedRoadmapAtomic.free IntegralMixedRoadmapAtomic.endBirth at *
  omega

theorem mid_producer_before_probe (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (j : ℕ)
    (hj : IntegralMixedRoadmapAtomic.depth q ≤ j) (hjn : j ≤ D q) :
    midProducer (D q) (N q) q j < IntegralMixedRoadmapProperRow.creating hn ht ha hR0 (pair q (BinaryNatCode.encode j)) :=by
  have HD:=IntegralMixedRoadmapAtomic.depth_le hn ht ha hR0 q hv
  have HE:=IntegralMixedRoadmapChain.rawStart_succ (D q) (IntegralMixedRoadmapAtomic.payload q) (levelIndex q)
  have HB:=IntegralMixedRoadmapChain.rawStart_bound (D q) (IntegralMixedRoadmapAtomic.payload q)
    (IntegralMixedRoadmapAtomic.depth q) (by omega)
  rw [creating_eq hn ht ha hR0 q hv j]
  unfold midProducer midFirst midBirth baseBirth IntegralMixedRoadmapChain.birth
  unfold IntegralMixedRoadmapChain.blockCount at HE
  unfold levelIndex at *
  have HK : IntegralMixedRoadmapAtomic.depth q-1+1=IntegralMixedRoadmapAtomic.depth q:=by omega
  rw [HK] at HE
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapProper

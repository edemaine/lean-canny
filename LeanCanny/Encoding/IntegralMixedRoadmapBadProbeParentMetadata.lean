/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent
public import LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
/-! # Original caps and dimensions of the actual reserved-parent bad snapshot -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B

theorem canonical (root : List Bool) :IntegralMixedHistory.Canonical (snapshot hn ht ha hR0 root).state:=
 IntegralMixedMarkedPrefixSnapshot.canonical hn ht ha hR0 root (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)

theorem ambient (root : List Bool) :(snapshot hn ht ha hR0 root).ambient=(P).ambient root:=rfl

theorem width (root : List Bool) :(snapshot hn ht ha hR0 root).width=(P).width root:=rfl

private theorem source_degree (root : List Bool) :
    (snapshot hn ht ha hR0 root).source.degree=(IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root).degree:=rfl

theorem packet_birth (base : List Bool) (hc :0<IntegralMixedRoadmapBadProbePacket.count base) :
    (snapshot hn ht ha hR0 (IntegralMixedRoadmapBadProbePacket.root base)).birth=
      IntegralMixedRoadmapBadProbePacket.creating ((P).ambient (IntegralMixedRoadmapBadProbePacket.root base)+5) base:=by
 have HCount :IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapBadProbePacket.root base)=
     IntegralMixedRoadmapBadProbePacket.count base:=by
   simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
     IntegralMixedRoadmapBadProbePacket.root,IntegralMixedRoadmapBadProbePacket.count,pairFst_pair,pairSnd_pair]
 rw [birth hn ht ha hR0 _ (hc.trans_eq HCount.symm)]
 unfold IntegralMixedMarkedPrefixFieldReadback.parent IntegralMixedRoadmapBadProbePacket.creating
 have HI :(P).ambient (IntegralMixedRoadmapBadProbePacket.root base)+5=
     IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapBadProbePacket.root base)+8:=by
   change IntegralMixedAuxiliaryMarkedIntegerSource.number n (IntegralMixedRoadmapBadProbePacket.root base)+3+5=_
   omega
 rw [HCount,HI]

theorem auxiliary_value (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((snapshot hn ht ha hR0 root).ambient+1)
      (snapshot hn ht ha hR0 root).source.degree=
    IntegralMixedExceptionalBounds.auxiliaryCap ((P).ambient root+1)
      (IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0 root).degree:=by
 rw [source_degree hn ht ha hR0,ambient hn ht ha hR0]

theorem auxiliary_cap (root : List Bool) :
    IntegralMixedExceptionalBounds.auxiliaryCap ((snapshot hn ht ha hR0 root).ambient+1)
      (snapshot hn ht ha hR0 root).source.degree≤2^(snapshot hn ht ha hR0 root).width:=by
 rw [source_degree hn ht ha hR0,ambient hn ht ha hR0,width hn ht ha hR0,IntegralMixedMarkedReservedCutView.degree hn ht ha hR0]
 exact IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0 root

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent

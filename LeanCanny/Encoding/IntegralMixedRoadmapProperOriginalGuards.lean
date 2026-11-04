/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperBadSound
/-! # Original-word meanings of the native order and no-bad guards -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
  IntegralMixedPhysicalFieldEquality.point field
  IntegralMixedPhysicalCutOrderedInterval.order IntegralMixedRoadmapProper.orderContext

theorem order_iff_original_fields (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hb : IntegralMixedRoadmapProper.OrderBounds hn ht ha hR0 q) :
    IntegralMixedRoadmapProper.order hn ht ha hR0 q=InfinitesimalSign.encode 1 ↔
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)<
        field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q) :=by
  have H:=IntegralMixedPhysicalCutOrderedInterval.order_iff hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapProper.orderContext hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.word q) (order_valid hn ht ha hR0 q hv)
    (order_selected_lt hn ht ha hR0 false q) (order_selected_lt hn ht ha hR0 true q)
  rw [order_endpoint hn ht ha hR0 false q hv hb.1,
    order_endpoint hn ht ha hR0 true q hv hb.2] at H
  simpa only [IntegralMixedRoadmapProper.order,Function.comp_apply,IntegralMixedRoadmapProper.orderQuery] using H

/-- This uses the original full word and its literal pre-probe snapshot.
No prepared query word or interpretation hom is part of the condition. -/
noncomputable def OriginalBadFree (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) : Prop:=
  ∀a,a∈Set.Ioo (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q))
    (field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q))→
    a∉IntegralMixedRoadmapBadProbeParent.bad hn ht ha hR0
      (IntegralMixedRoadmapAtomic.root q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)

private theorem parent_point_congr (a b u v : List Bool) (hab : a=b) (huv : u=v)
    (ha' : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context a) u)
    (hb' : SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (IntegralMixedMarkedPrefixFieldReadback.context b) v) :
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 a u ha'=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 b v hb':=by
  subst b
  subst v
  rfl

theorem noBad_iff_original_bad_free (q : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 (rowKey q))
    (hab : field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer false q)<
      field hn ht ha hR0 q hv (IntegralMixedRoadmapProper.producer true q)) :
    IntegralMixedRoadmapProper.NoBad hn ht ha hR0 q ↔ OriginalBadFree hn ht ha hR0 q hv :=by
  obtain ⟨codes,last,Hraw⟩:=bad_raw_domain hn ht ha hR0 q hv
  have HFit : ∀side,IntegralMixedRoadmapBadProbePacket.producer side (IntegralMixedRoadmapProper.badPacket q)<
      IntegralMixedMarkedPrefixFieldReadback.parent n
        (IntegralMixedRoadmapBadProbePacket.root (IntegralMixedRoadmapProper.badPacket q)):=by
    intro side
    rw [bad_packet_producer,IntegralMixedRoadmapProper.badPacket_root]
    exact bad_producer_lt_parent hn ht ha hR0 q HR side
  have HOrder : IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
      (bad_full_valid hn ht ha hR0 q hv) false<
    IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (IntegralMixedRoadmapProper.badPacket q)
      (bad_full_valid hn ht ha hR0 q hv) true:=by
    rw [bad_endpoint hn ht ha hR0 q hv HR false,bad_endpoint hn ht ha hR0 q hv HR true]
    exact hab
  have H:=IntegralMixedRoadmapBadProbeSemantics.noBadProbe_iff hn ht ha hR0
    (IntegralMixedRoadmapProper.badPacket q) codes last Hraw (bad_full_valid hn ht ha hR0 q hv) HFit HOrder
  have HLabels : IntegralMixedRoadmapBadProbePacket.labels (IntegralMixedRoadmapProper.badPacket q)=
      IntegralMixedRoadmapProper.labels q:=by
    simp only [IntegralMixedRoadmapBadProbePacket.labels,IntegralMixedRoadmapProper.badPacket,
      IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  have HP:=parent_point_congr hn ht ha hR0 _ _ _ _ (IntegralMixedRoadmapProper.badPacket_root q)
    (bad_packet_word q) (bad_full_valid hn ht ha hR0 q hv) (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
  unfold OriginalBadFree
  unfold IntegralMixedRoadmapBadProbeParent.bad at H ⊢
  rw [HP,IntegralMixedRoadmapProper.badPacket_root,HLabels,
    bad_endpoint hn ht ha hR0 q hv HR false,bad_endpoint hn ht ha hR0 q hv HR true] at H
  exact H

end LeanCanny.Encoding.IntegralMixedRoadmapLocalFrame

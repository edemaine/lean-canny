/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperMidpointCaptures
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowParent
public import LeanCanny.Encoding.IntegralMixedRoadmapChainRoom
/-! # Actual MID and child producers precede the reserved row probe -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedRoadmapProper
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "D"=>FormulaSignSlotRadialProviderAtomic.dimension
local notation "N"=>FormulaSignSlotRadialProviderAtomic.initial
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial

private theorem raw_depth (q :List Bool) :IntegralMixedRoadmapAtomic.depth q=FormulaSignSlotRadialProviderAtomic.depth q:=rfl
private theorem raw_payload (q :List Bool) :IntegralMixedRoadmapAtomic.payload q=FormulaSignSlotRadialProviderAtomic.payload q:=rfl

theorem creating_eq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) (j : ℕ) :
    FormulaSignSlotRadialProviderProperRow.creating (pair q (BinaryNatCode.encode j))=
      N q+IntegralMixedRoadmapRecordChain.recordBound (D q) :=by
  have HR:=FormulaSignSlotRadialProviderAtomic.raw_count q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  unfold FormulaSignSlotRadialProviderProperRow.creating IntegralMixedRoadmapBadProbePacket.creating
  simp only [FormulaSignSlotRadialProviderProperRow.initial,FormulaSignSlotRadialProviderProperRow.atomic,
    FormulaSignSlotRadialProviderProperRow.oldPacket,badPacket,IntegralMixedRoadmapBadProbePacket.count,
    IntegralMixedRoadmapBadProbePacket.raw,IntegralMixedRoadmapBadProbePacket.packet,pairFst_pair,pairSnd_pair]
  simp only [raw_payload]
  rw [HR]
  unfold IntegralMixedRoadmapRecordChain.probedRecordBound
  omega

theorem child_producer_before_probe (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (j : ℕ) (hj : FormulaSignSlotRadialProviderAtomic.depth q ≤ j) (hjn : j ≤ D q) :
    childProducer (D q) (N q) q j < FormulaSignSlotRadialProviderProperRow.creating (pair q (BinaryNatCode.encode j)) :=by
  have HD:=FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HE:=FormulaSignSlotRadialProviderAtomic.latest_block_end q hv
  have HB:=IntegralMixedRoadmapChain.rawStart_bound (D q) (FormulaSignSlotRadialProviderAtomic.payload q)
    (FormulaSignSlotRadialProviderAtomic.depth q) (by omega)
  rw [creating_eq q hv j]
  dsimp only [childProducer,FormulaSignSlotRadialProviderAtomic.free,FormulaSignSlotRadialProviderAtomic.endBirth,
    FormulaSignSlotRadialProviderAtomic.first,IntegralMixedRoadmapAtomic.free,IntegralMixedRoadmapAtomic.endBirth,
    IntegralMixedRoadmapAtomic.first] at *
  simp only [raw_depth,raw_payload] at *
  omega

theorem mid_producer_before_probe (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (hd : 0<FormulaSignSlotRadialProviderAtomic.depth q) (j : ℕ)
    (hj : FormulaSignSlotRadialProviderAtomic.depth q ≤ j) (hjn : j ≤ D q) :
    midProducer (D q) (N q) q j < FormulaSignSlotRadialProviderProperRow.creating (pair q (BinaryNatCode.encode j)) :=by
  have HD:=FormulaSignSlotRadialProviderAtomic.depth_le q (FormulaSignSlotRadialProviderAtomic.valid_grammar q hv)
  have HE:=IntegralMixedRoadmapChain.rawStart_succ (D q) (FormulaSignSlotRadialProviderAtomic.payload q) (levelIndex q)
  have HB:=IntegralMixedRoadmapChain.rawStart_bound (D q) (FormulaSignSlotRadialProviderAtomic.payload q)
    (FormulaSignSlotRadialProviderAtomic.depth q) (by omega)
  rw [creating_eq q hv j]
  unfold midProducer midFirst midBirth baseBirth IntegralMixedRoadmapChain.birth
  unfold IntegralMixedRoadmapChain.blockCount at HE
  unfold levelIndex at *
  simp only [raw_depth,raw_payload] at HE ⊢
  have HK : FormulaSignSlotRadialProviderAtomic.depth q-1+1=FormulaSignSlotRadialProviderAtomic.depth q:=by omega
  rw [HK] at HE
  omega

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProper

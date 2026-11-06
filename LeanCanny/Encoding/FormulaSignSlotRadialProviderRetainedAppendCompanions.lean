/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendCorrelation
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPacket
/-! # The fresh retained child satisfies its actual latest companion scan -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source

theorem latest_free_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.free (dimension old) (packet (dimension old) old e w)=dimension old-depth old := by
  unfold IntegralMixedRoadmapAtomic.free
  have HD : IntegralMixedRoadmapAtomic.depth (packet (dimension old) old e w)=depth old+1 := depth_packet _ _ _ _
  rw [HD]
  omega

theorem latest_anchor_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapAtomic.anchor (dimension old) (N old) (packet (dimension old) old e w)=
      N old+start old+1+(dimension old-depth old) := by
  have HE : IntegralMixedRoadmapAtomic.endBirth (dimension old) (N old)
      (packet (dimension old) old e w)=finishBirth old e := by
    unfold finishBirth FormulaSignSlotRadialProviderAtomic.endBirth IntegralMixedRoadmapAtomic.endBirth
    change N old+IntegralMixedRoadmapChain.rawStart (dimension old)
        (FormulaSignSlotRadialProviderAtomic.payload (packet (dimension old) old e w))
        (depth (packet (dimension old) old e w))=
      N old+IntegralMixedRoadmapChain.rawStart (dimension old)
        (FormulaSignSlotRadialProviderAtomic.payload (packet (dimension old) old e []))
        (depth (packet (dimension old) old e []))
    simp only [payload_packet,depth_packet]
  unfold IntegralMixedRoadmapAtomic.anchor
  rw [HE,latest_free_packet,finish_eq,begin_eq]
  omega

theorem companion_query_packet (old : List Bool) (e : ℕ) (w : List Bool) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (dimension (packet (dimension old) old e w)) (N (packet (dimension old) old e w)) (packet (dimension old) old e w)=
      LeanCanny.pair (LeanCanny.pair (C (preparedRoot old e)) w)
        (IntegralMixedPhysicalPointCompanionScan.descriptor
          (N old+start old+1+(dimension old-depth old))
          (N old+start old+1+(dimension old-depth old)+1) (dimension old-depth old)) := by
  rw [dimension_packet,initial_packet]
  unfold FormulaSignSlotRadialProviderAtomic.companionQuery FormulaSignSlotRadialProviderAtomic.first
    FormulaSignSlotRadialProviderAtomic.anchor FormulaSignSlotRadialProviderAtomic.free IntegralMixedRoadmapAtomic.first
  rw [sample_query_packet,latest_anchor_packet,latest_free_packet]

attribute [local irreducible] parentState parentTuple parentValues parentHom parentCommands parentDescriptor

theorem WordReceipt.latest_companions
    {old : List Bool} {hv : A old} {hd : depth old<dimension old}
    {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
    {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ} (W : WordReceipt old hv hd e he p) :
    FormulaSignSlotRadialProviderAtomic.companionQuery
      (dimension (packet (dimension old) old e W.word)) (N (packet (dimension old) old e W.word))
      (packet (dimension old) old e W.word)∈FormulaSignSlotRadialProviderAtomic.Companions.language := by
  rw [companion_query_packet]
  have HF := finish_eq old e
  have HB := begin_eq old
  have HA := (child_anchor_metadata old hv hd e he).1
  have HFit : N old+start old+1+(dimension old-depth old)+1+(dimension old-depth old)≤
      prefixLength (B).parameters ((B).key (C (preparedRoot old e))) := by
    rw [FormulaSignSlotRadialProviderRecordPrefix.full_prefix]
    have H := finish_le_full old hv hd e he
    change finishBirth old e≤FormulaSignSlotRadialProviderRecordPlan.fullCount (preparedRoot old e) at H
    omega
  apply (FormulaSignSlotRadialProviderAtomic.companion_language_packet_iff
    (C (preparedRoot old e)) W.word W.valid _ _ _ HA HFit).mpr
  intro j hj
  have HJ0 : N old+start old≤N old+start old+1+(dimension old-depth old)+1+j := by omega
  have HJ1 : N old+start old+1+(dimension old-depth old)+1+j<finishBirth old e := by omega
  have HJA := active_after_begin old hv hd e he _ HJ0 (HJ1.trans_le (finish_le_full old hv hd e he))
  refine ⟨HJA,?_,?_⟩
  · exact (W.local_geometric_point _ HJ0 HJ1).trans
      (W.local_geometric_point _ (by omega) (by omega)).symm
  · rw [W.local_geometric_point _ (by omega) (by omega)]
    exact W.local_correlation _ HJ0 HJ1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend

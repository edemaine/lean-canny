/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendMidpointHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendScans
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendBounds
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPacket
/-! # The actual appended MID guard follows from one fresh joint word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem mid_birth_payload (d initial : ℕ) (q r : List Bool)
    (h : IntegralMixedRoadmapAtomic.payload q=IntegralMixedRoadmapAtomic.payload r) :
    IntegralMixedRoadmapProper.midBirth d initial q=IntegralMixedRoadmapProper.midBirth d initial r :=by
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
    IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.levelIndex IntegralMixedRoadmapAtomic.depth
  rw [h]

private theorem mid_count_payload (d : ℕ) (q r : List Bool)
    (h : IntegralMixedRoadmapAtomic.payload q=IntegralMixedRoadmapAtomic.payload r) :
    IntegralMixedRoadmapProper.captureCount d q=IntegralMixedRoadmapProper.captureCount d r :=by
  unfold IntegralMixedRoadmapProper.captureCount IntegralMixedRoadmapProper.levelIndex IntegralMixedRoadmapAtomic.depth
  rw [h]

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointCompanionScan.retained
  preparedRoot context beginBirth finishBirth fullBirth

theorem midpoint_of_fresh_readback (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (p p0 : Fin ((P).ambient (pairFst ((B).key (CTX old e)))+1)→ℝ)
    (hr : FreshReadback hn ht ha hR0 old e w hw p p0) :
    IntegralMixedRoadmapProper.Midpoint hn ht ha hR0 (packet (D old) old e w) :=by
  let q:=packet (D old) old e w
  let a:=beginBirth hn ht ha hR0 old
  let k:=D old-IntegralMixedRoadmapAtomic.depth old
  have HPayload : IntegralMixedRoadmapAtomic.payload q=IntegralMixedRoadmapAtomic.payload (packet (D old) old e []):=by
    simp only [q,payload_packet]
  have HB : IntegralMixedRoadmapProper.midBirth (D old) (N old) q=a:=
    (mid_birth_payload (D old) (N old) _ _ HPayload).trans (midpoint_birth hn ht ha hR0 old e)
  have HF : IntegralMixedRoadmapProper.midFirst (D old) (N old) q=a+1:=by
    unfold IntegralMixedRoadmapProper.midFirst
    rw [HB]
  have HK : IntegralMixedRoadmapProper.captureCount (D old) q=k:=
    (mid_count_payload (D old) _ _ HPayload).trans (midpoint_count hn ht ha hR0 old e)
  have HA:=midpoint_anchor_active hn ht ha hR0 old hv hd e he w
  have HAnchor : IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) a:=
    Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b) HB) HA
  have HCapture : ∀j,j<k→IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) (a+1+j):=by
    intro j hj
    have HJ : j<IntegralMixedRoadmapProper.captureCount (D old) q:=hj.trans_eq HK.symm
    have H:=midpoint_capture_active hn ht ha hR0 old hv hd e he w j HJ
    exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b)
      (congrArg (fun b=>b+j) HF)) H
  have HE : finishBirth hn ht ha hR0 old e=a+2+2*k:=finish_eq hn ht ha hR0 old e
  have HEnd:=finish_le_full hn ht ha hR0 old hv hd e he
  have HScan:=companion_of_fresh_readback hn ht ha hR0 old e w hw p p0 hr a (a+1) k
    (Nat.le_refl _) (by omega) (by omega) (by omega) HEnd HAnchor HCapture
  have HSample : IntegralMixedRoadmapAtomic.sampleQuery q=pair (CTX old e) w:=by
    unfold IntegralMixedRoadmapAtomic.sampleQuery
    rw [packet_context hn ht ha hR0 old e w,word_packet]
  have HQuery : IntegralMixedRoadmapProper.midCompanions
      (D q) (N q) q=pair (pair (CTX old e) w) (IntegralMixedPhysicalPointCompanionScan.descriptor a (a+1) k):=by
    have HDim:=dimension_packet hn ht ha hR0 (D old) old e w
    have HInit:=initial_packet hn ht ha hR0 (D old) old e w
    rw [HDim,HInit]
    unfold IntegralMixedRoadmapProper.midCompanions
    rw [HB,HF,HK,HSample]
  change IntegralMixedRoadmapProper.midCompanions (D q) (N q) q∈_
  rw [HQuery]
  exact HScan

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

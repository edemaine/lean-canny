/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedMidpoint
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNativeHeader
/-! # Actual appended MID codes activate without assuming the new vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context

theorem midpoint_checked (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool) :
    IntegralMixedRoadmapChain.Checked (D old)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 (packet (D old) old e w))
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 (packet (D old) old e w)) (N old)
      (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha old)
      (IntegralMixedRoadmapAtomic.payload (packet (D old) old e w)) :=by
  simpa only [payload_packet] using checked hn ht ha hR0 old hv hd e he w

theorem midpoint_positive (old : List Bool) (e : ℕ) (w : List Bool) :
    0<IntegralMixedRoadmapAtomic.depth (packet (D old) old e w) :=by
  rw [depth_packet]
  omega

theorem midpoint_records (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (ROOT old e)=
      IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload (packet (D old) old e w)) :=by
  simp only [IntegralMixedCausalRecordPlanBits.records,preparedRoot,IntegralMixedRoadmapAtomic.root,
    payload_packet,pairFst_pair,pairSnd_pair]

theorem midpoint_birth_index (old : List Bool) (e : ℕ) (w : List Bool) :
    IntegralMixedRoadmapProper.midBirth (D old) (N old) (packet (D old) old e w)=
      number n (ROOT old e)+8+IntegralMixedRoadmapProper.midRawIndex (D old) (packet (D old) old e w) :=by
  unfold IntegralMixedRoadmapProper.midBirth IntegralMixedRoadmapProper.baseBirth
    IntegralMixedRoadmapChain.birth IntegralMixedRoadmapProper.midRawIndex
  rw [initial_root]
  omega

theorem midpoint_companion_birth_index (old : List Bool) (e : ℕ) (w : List Bool) (i : ℕ) :
    IntegralMixedRoadmapProper.midFirst (D old) (N old) (packet (D old) old e w)+i=
      number n (ROOT old e)+8+(IntegralMixedRoadmapProper.midRawIndex (D old) (packet (D old) old e w)+1+i) :=by
  have H:=midpoint_birth_index hn ht ha hR0 old e w
  unfold IntegralMixedRoadmapProper.midFirst
  omega

theorem midpoint_anchor_active (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapProper.midBirth (D old) (N old) (packet (D old) old e w)) :=by
  let q:=packet (D old) old e w
  let i:=IntegralMixedRoadmapProper.midRawIndex (D old) q
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he w
  have HD:=midpoint_positive hn ht ha hR0 old e w
  have HG:=IntegralMixedRoadmapProper.checked_midpoint_good HC HD
  have HF:=IntegralMixedRoadmapProper.checked_midpoint_fit HC HD
  have HW:=IntegralMixedRoadmapProper.checked_midpoint_record HC HD
  have HB:=midpoint_birth_index hn ht ha hR0 old e w
  have HN:=dimension_root hn ht ha hR0 old e
  have HI : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [midpoint_records hn ht ha hR0 old e w]
    exact HF
  have HG' : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) (IntegralMixedRoadmapProper.labels q)
      (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
      (IntegralMixedRoadmapProper.levelIndex q+1) (IntegralMixedRoadmapProper.levelIndex q+1):=by
    exact Eq.mp (congrArg₂ (fun d b=>IntegralMixedChronologicalMidpointCode.Good d b
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q+1)
      (IntegralMixedRoadmapProper.levelIndex q+1)) HN.symm HB) HG
  have HW' : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (ROOT old e)) (IntegralMixedRoadmapProper.labels q)
        (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
        (IntegralMixedRoadmapProper.levelIndex q+1) (IntegralMixedRoadmapProper.levelIndex q+1):=by
    rw [IntegralMixedCausalRecordPlanBits.code,midpoint_records hn ht ha hR0 old e w,HN]
    exact HW
  have HA:=midpoint_active hn ht ha hR0 old e i HI _ _ _ _ _ HG' HW'
  exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b) HB.symm) HA

theorem midpoint_capture_active (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool) (j : ℕ)
    (hj : j<IntegralMixedRoadmapProper.captureCount (D old) (packet (D old) old e w)) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapProper.midFirst (D old) (N old) (packet (D old) old e w)+j) :=by
  let q:=packet (D old) old e w
  let i:=IntegralMixedRoadmapProper.midRawIndex (D old) q+1+j
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he w
  have HD:=midpoint_positive hn ht ha hR0 old e w
  have HG:=IntegralMixedRoadmapProper.checked_midpoint_companion_good HC HD j hj
  have HF:=IntegralMixedRoadmapProper.checked_midpoint_companion_fit HC HD j hj
  have HW:=IntegralMixedRoadmapProper.checked_midpoint_companion_record HC HD j hj
  have HB:=midpoint_companion_birth_index hn ht ha hR0 old e w j
  have HN:=dimension_root hn ht ha hR0 old e
  have HI : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [midpoint_records hn ht ha hR0 old e w]
    exact HF
  have HG' : IntegralMixedChronologicalMidpointCode.Good ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) (IntegralMixedRoadmapProper.labels q)
      (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
      (IntegralMixedRoadmapProper.levelIndex q+1) (D old-j):=by
    exact Eq.mp (congrArg₂ (fun d b=>IntegralMixedChronologicalMidpointCode.Good d b
      (IntegralMixedRoadmapProper.labels q) (IntegralMixedRoadmapProper.producer false q)
      (IntegralMixedRoadmapProper.producer true q) (IntegralMixedRoadmapProper.levelIndex q+1)
      (D old-j)) HN.symm HB) HG
  have HW' : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (ROOT old e)) (IntegralMixedRoadmapProper.labels q)
        (IntegralMixedRoadmapProper.producer false q) (IntegralMixedRoadmapProper.producer true q)
        (IntegralMixedRoadmapProper.levelIndex q+1) (D old-j):=by
    rw [IntegralMixedCausalRecordPlanBits.code,midpoint_records hn ht ha hR0 old e w,HN]
    exact HW
  have HA:=midpoint_active hn ht ha hR0 old e i HI _ _ _ _ _ HG' HW'
  exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b) HB.symm) HA

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedChild
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendMidpointHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendBounds
/-! # Actual child anchor and captures activate before vertex acceptance -/
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
local notation "Q"=>(fun old e=>packet (D old) old e [])
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial preparedRoot context IntegralMixedRoadmapAtomic.anchor
  IntegralMixedRoadmapAtomic.first IntegralMixedRoadmapAtomic.free

private theorem initial_le_begin (old : List Bool) : N old≤beginBirth hn ht ha hR0 old:=by
  unfold beginBirth IntegralMixedRoadmapAtomic.endBirth
  omega

private theorem active_at_frame_record (old : List Bool) (e b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood (D old) b labels g j)
    (hw : WordList.get (IntegralMixedCausalRecordPlanBits.records (ROOT old e)) (b-N old)=
      IntegralMixedChronologicalFrameCode.code (D old) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e) b:=by
  let i:=b-N old
  have HB : b=number n (ROOT old e)+8+i:=by rw [initial_root];dsimp only [i];omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    unfold fullBirth at hb1
    rw [initial_root] at hb1
    dsimp only [i]
    omega
  have HN:=dimension_root hn ht ha hR0 old e
  have HG : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) labels g j:=
    Eq.mp (congrArg₂ (fun d b=>IntegralMixedChronologicalFrameCode.PointGood d b labels g j) HN.symm HB) hg
  have HW : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (ROOT old e)) labels g j:=by
    rw [IntegralMixedCausalRecordPlanBits.code,HN]
    exact hw
  have HA:=frame_active hn ht ha hR0 old e i HI labels g j HG HW
  exact Eq.mp (congrArg (fun b=>IntegralMixedPhysicalPointCompanionScan.Active hn ht ha
    (radius_binary hR0) false (CTX old e) b) HB.symm) HA

theorem child_anchor_active (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapAtomic.anchor (D old) (N old) (Q old e)):=by
  let q:=Q old e
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he []
  have HPositive:=midpoint_positive hn ht ha hR0 old e []
  have HG:=IntegralMixedRoadmapAtomic.anchor_point_good (q:=q) HC
  have HW:=IntegralMixedRoadmapAtomic.checked_anchor_record (q:=q) HC HPositive
  have HInitial:=initial_le_begin hn ht ha hR0 old
  have HFinish:=finish_le_full hn ht ha hR0 old hv hd e he
  have HB0 : N old≤IntegralMixedRoadmapAtomic.anchor (D old) (N old) q:=by
    dsimp only [q]
    rw [child_anchor]
    omega
  have HB1 : IntegralMixedRoadmapAtomic.anchor (D old) (N old) q<fullBirth hn ht ha hR0 old e:=by
    dsimp only [q]
    rw [child_anchor]
    rw [finish_eq] at HFinish
    omega
  apply active_at_frame_record hn ht ha hR0 old e _ HB0 HB1 _ _ _ HG
  rw [midpoint_records hn ht ha hR0 old e []]
  exact HW

theorem child_capture_active (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (j : ℕ)
    (hj : j<IntegralMixedRoadmapAtomic.free (D old) (Q old e)) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e)+j):=by
  let q:=Q old e
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he []
  have HG:=IntegralMixedRoadmapAtomic.capture_point_good (q:=q) HC j hj
  have HW:=IntegralMixedRoadmapAtomic.latest_capture_record (q:=q) HC j hj
  have HInitial:=initial_le_begin hn ht ha hR0 old
  have HFinish:=finish_le_full hn ht ha hR0 old hv hd e he
  have HJ : j<D old-IntegralMixedRoadmapAtomic.depth old:=by simpa only [child_count] using hj
  have HB0 : N old≤IntegralMixedRoadmapAtomic.first (D old) (N old) q+j:=by
    dsimp only [q]
    rw [IntegralMixedRoadmapAtomic.first,child_anchor]
    omega
  have HB1 : IntegralMixedRoadmapAtomic.first (D old) (N old) q+j<fullBirth hn ht ha hR0 old e:=by
    dsimp only [q]
    rw [IntegralMixedRoadmapAtomic.first,child_anchor]
    rw [finish_eq] at HFinish
    omega
  have HF : N old≤IntegralMixedRoadmapAtomic.first (D old) (N old) q:=by
    dsimp only [q]
    rw [IntegralMixedRoadmapAtomic.first,child_anchor]
    omega
  apply active_at_frame_record hn ht ha hR0 old e _ HB0 HB1 _ _ _ HG
  rw [midpoint_records hn ht ha hR0 old e []]
  have HI : IntegralMixedRoadmapAtomic.first (D old) (N old) q+j-N old=
      IntegralMixedRoadmapAtomic.first (D old) (N old) q-N old+j:=by omega
  rw [HI]
  exact HW

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

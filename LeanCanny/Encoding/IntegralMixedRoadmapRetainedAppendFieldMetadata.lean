/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendChildHeader
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendNoCut
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointCriticalReadback
/-! # Actual selected coordinates of retained-append critical bytes -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "ROOT"=>preparedRoot hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "Q"=>(fun old e=>packet (D old) old e [])
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot context
  IntegralMixedFramedHistoryFamilyBits.family

theorem selected_frame_code (old :List Bool) (e i :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count (ROOT old e)) (labels :List Bool) (g j :ℕ)
    (hg :IntegralMixedChronologicalFrameCode.PointGood ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) labels g j)
    (hw :IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (ROOT old e)) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (number n (ROOT old e)+8+i)=j :=by
  unfold IntegralMixedPhysicalPointCompanionScan.selected
  rw [native_header]
  have HC:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (ROOT old e) i hi labels g j hg hw
  unfold IntegralMixedRoadmapSeedMetadata.stageHeader
  rw [HC]
  exact IntegralMixedChronologicalFrame.raw_selected _ labels g j hg

theorem selected_midpoint_code (old :List Bool) (e i :ℕ)
    (hi :i<IntegralMixedCausalRecordPlanBits.count (ROOT old e)) (labels :List Bool) (a b g j :ℕ)
    (hg :IntegralMixedChronologicalMidpointCode.Good ((P).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) labels a b g j)
    (hw :IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalMidpointCode.code ((P).ambient (ROOT old e)) labels a b g j) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (number n (ROOT old e)+8+i)=j :=by
  unfold IntegralMixedPhysicalPointCompanionScan.selected
  rw [native_header]
  have HC:=IntegralMixedMarkedMidpointReceipt.critical hn ht ha hR0 (ROOT old e) i hi labels a b g j hg hw
  unfold IntegralMixedRoadmapSeedMetadata.stageHeader
  rw [HC]
  exact IntegralMixedChronologicalMidpoint.raw_selected _ labels a b g j hg

theorem midpoint_anchor_selected (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapProper.midBirth (D old) (N old) (packet (D old) old e w))=IntegralMixedRoadmapProper.levelIndex (packet (D old) old e w)+1 :=by
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
  have HA:=selected_midpoint_code hn ht ha hR0 old e i HI _ _ _ _ _ HG' HW'
  exact (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)) HB).trans HA

theorem midpoint_capture_selected (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool) (j : ℕ)
    (hj : j<IntegralMixedRoadmapProper.captureCount (D old) (packet (D old) old e w)) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapProper.midFirst (D old) (N old) (packet (D old) old e w)+j)=D old-j :=by
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
  have HA:=selected_midpoint_code hn ht ha hR0 old e i HI _ _ _ _ _ HG' HW'
  exact (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)) HB).trans HA

private theorem selected_at_frame_record (old : List Bool) (e b : ℕ)
    (hb0 : N old≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood (D old) b labels g j)
    (hw : WordList.get (IntegralMixedCausalRecordPlanBits.records (ROOT old e)) (b-N old)=
      IntegralMixedChronologicalFrameCode.code (D old) labels g j) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e) b=j :=by
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
  have HA:=selected_frame_code hn ht ha hR0 old e i HI labels g j HG HW
  exact (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)) HB).trans HA

theorem child_anchor_selected (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapAtomic.anchor (D old) (N old) (Q old e))=IntegralMixedRoadmapAtomic.depth (Q old e) :=by
  let q:=Q old e
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he []
  have HPositive:=midpoint_positive hn ht ha hR0 old e []
  have HG:=IntegralMixedRoadmapAtomic.anchor_point_good (q:=q) HC
  have HW:=IntegralMixedRoadmapAtomic.checked_anchor_record (q:=q) HC HPositive
  have HInitial :N old≤beginBirth hn ht ha hR0 old:=by unfold beginBirth IntegralMixedRoadmapAtomic.endBirth;omega
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
  apply selected_at_frame_record hn ht ha hR0 old e _ HB0 HB1 _ _ _ HG
  rw [midpoint_records hn ht ha hR0 old e []]
  exact HW

theorem child_capture_selected (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (j : ℕ)
    (hj : j<IntegralMixedRoadmapAtomic.free (D old) (Q old e)) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)
      (IntegralMixedRoadmapAtomic.first (D old) (N old) (Q old e)+j)=D old-j :=by
  let q:=Q old e
  have HC:=midpoint_checked hn ht ha hR0 old hv hd e he []
  have HG:=IntegralMixedRoadmapAtomic.capture_point_good (q:=q) HC j hj
  have HW:=IntegralMixedRoadmapAtomic.latest_capture_record (q:=q) HC j hj
  have HInitial :N old≤beginBirth hn ht ha hR0 old:=by unfold beginBirth IntegralMixedRoadmapAtomic.endBirth;omega
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
  apply selected_at_frame_record hn ht ha hR0 old e _ HB0 HB1 _ _ _ HG
  rw [midpoint_records hn ht ha hR0 old e []]
  have HI : IntegralMixedRoadmapAtomic.first (D old) (N old) q+j-N old=
      IntegralMixedRoadmapAtomic.first (D old) (N old) q-N old+j:=by omega
  rw [HI]
  exact HW

private theorem empty_field_point_good (d b :ℕ) :IntegralMixedChronologicalFrameCode.PointGood d b [] 0 0 :=by
  simp [IntegralMixedChronologicalFrameCode.PointGood,IntegralMixedChronologicalFrameCode.Good,WordListRecords.count]

theorem seed_selected_after_finish (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (b : ℕ)
    (hb0 : finishBirth hn ht ha hR0 old e≤b) (hb1 : b<fullBirth hn ht ha hR0 old e) :
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e) b=0 :=by
  let i:=b-N old
  have HN:=initial_root hn ht ha hR0 old e
  have HI0 : N old≤b:=by
    have H:=finish_eq hn ht ha hR0 old e
    have HL : N old≤beginBirth hn ht ha hR0 old:=by unfold beginBirth IntegralMixedRoadmapAtomic.endBirth;omega
    omega
  have HB : b=number n (ROOT old e)+8+i:=by rw [HN];dsimp only [i];omega
  have HI : i<IntegralMixedCausalRecordPlanBits.count (ROOT old e):=by
    unfold fullBirth at hb1
    rw [HN] at hb1
    dsimp only [i]
    omega
  have HDIM:=dimension_root hn ht ha hR0 old e
  have HG : IntegralMixedChronologicalFrameCode.PointGood
      ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient (ROOT old e))
      (number n (ROOT old e)+8+i) [] 0 0:=empty_field_point_good _ _
  have HW : IntegralMixedCausalRecordPlanBits.code (ROOT old e) i=
      IntegralMixedChronologicalFrameCode.code
        ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)).ambient (ROOT old e)) [] 0 0:=by
    rw [HDIM]
    exact seed_code_after_finish hn ht ha hR0 old hv hd e he b hb0 hb1
  have HA:=selected_frame_code hn ht ha hR0 old e i HI [] 0 0 HG HW
  exact (congrArg (IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX old e)) HB).trans HA

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

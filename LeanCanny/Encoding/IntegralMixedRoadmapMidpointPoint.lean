/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointCaptures
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointSource
/-! # Physical midpoint coordinates in the candidate's native dimension -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "N"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
 IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial
 IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalFieldEquality.point
 IntegralFramedPhysicalSquare.point

noncomputable def midpointPoint (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q) : Fin (D q+1)→ℝ:=fun i=>
  IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q)
    (Fin.cast (congrArg (·+1) (IntegralMixedRoadmapAtomic.native_dimension hn ht ha hR0 q)).symm i)

theorem midpointPoint_frozen (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (HM : Midpoint hn ht ha hR0 q)
    (i : Fin (D q+1)) (hi : i.val < levelIndex q) :
    midpointPoint hn ht ha hR0 q hv i=IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv)
      (Nat.fromBitsLE (WordList.get (labels q) i.val)) :=by
  have HA:=(midpoint_sound hn ht ha hR0 q HM).choose_spec.1
  have HG:=midpoint_context_good hn ht ha hR0 q hv hd
  have HF:=IntegralMixedPhysicalPointCompanionScan.midpoint_frame_point hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q) HA
    (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) HG
    (midpoint_context_command hn ht ha hR0 q hv hd)
  have HI : i.val < WordListRecords.count (labels q):=by rw [labels_count];exact hi
  have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (midBirth (D q) (N q) q) HA).1
  have HJ:=(HG.1.2 i.val HI).trans HB
  rw [IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) _ _ _ _ HJ]
  exact HF.2.1 i.val HI

theorem midpointPoint_free (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (HM : Midpoint hn ht ha hR0 q)
    (i : Fin (D q+1)) (hi : levelIndex q < i.val) :
    midpointPoint hn ht ha hR0 q hv i=IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
      (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
      (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midProducer (D q) (N q) q i.val) :=by
  have HC : D q-i.val < captureCount (D q) q:=by unfold captureCount;omega
  have H:=midpoint_capture_readback hn ht ha hR0 q hv hd HM (D q-i.val) HC
  have HE : D q-(D q-i.val)=i.val:=by omega
  unfold midpointPoint midProducer
  convert H.symm using 1
  apply congrArg (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q))
  exact Fin.ext (by simpa only [Fin.val_cast] using HE.symm)


theorem midpointPoint_height (q : List Bool) (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 q)
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (HM : Midpoint hn ht ha hR0 q)
    (i : Fin (D q+1)) (hi : i.val=levelIndex q) :
    midpointPoint hn ht ha hR0 q hv i=
      (IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (producer false q)+
       IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
        (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
        (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (producer true q))/2 :=by
  have HA:=(midpoint_sound hn ht ha hR0 q HM).choose_spec.1
  have HG:=midpoint_context_good hn ht ha hR0 q hv hd
  have HF:=IntegralMixedPhysicalPointCompanionScan.midpoint_frame_point hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q) HA
    (labels q) (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) HG
    (midpoint_context_command hn ht ha hR0 q hv hd)
  have HB:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (midBirth (D q) (N q) q) HA).1
  rw [IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) _ _ _ _ (HG.2.1.trans HB),
    IntegralMixedPhysicalFieldEquality.point_full hn ht ha (radius_binary hR0) _ _ _ _ (HG.2.2.1.trans HB)]
  unfold midpointPoint
  convert HF.2.2.1 using 1
  apply congrArg (IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
    (IntegralMixedRoadmapAtomic.context q) (IntegralMixedRoadmapAtomic.word q)
    (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 q hv) (midBirth (D q) (N q) q))
  exact Fin.ext (by simpa only [Fin.val_cast,labels_count] using hi)

end LeanCanny.Encoding.IntegralMixedRoadmapProper

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperMidpointCaptures
/-! # Checked syntax determines MID headers before accepting a new vertex -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProper
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {d B sourceCap initial C : ℕ} {q : List Bool}

private theorem checked_latest_lt (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    levelIndex q<IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload q) :=by
  change IntegralMixedRoadmapAtomic.depth q-1<IntegralMixedRoadmapAtomic.depth q
  omega

theorem checked_midpoint_good
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    IntegralMixedChronologicalMidpointCode.Good d (midBirth d initial q) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (levelIndex q+1) :=by
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_anchor
    (IntegralMixedRoadmapChain.level_checked h (levelIndex q) (checked_latest_lt hd))
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc] using H

theorem checked_midpoint_companion_good
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount d q) :
    IntegralMixedChronologicalMidpointCode.Good d (midFirst d initial q+i) (labels q)
      (producer false q) (producer true q) (levelIndex q+1) (d-i) :=by
  have Hlevel:=IntegralMixedRoadmapChain.level_checked h (levelIndex q) (checked_latest_lt hd)
  have HQ : IntegralMixedRoadmapLevel.freeCount d
      (IntegralMixedRoadmapChain.levelPacket d (IntegralMixedRoadmapAtomic.payload q) (levelIndex q))=captureCount d q :=by
    simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k,captureCount]
    omega
  have H:=IntegralMixedRoadmapLevel.checked_midpoint_companion Hlevel i (by rw [HQ];exact hi)
  simpa only [IntegralMixedRoadmapLevel.afterEndpoints,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.g,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,
    labels,producer,midFirst,midBirth,baseBirth,IntegralMixedRoadmapChain.freshCount,Nat.add_assoc] using H

theorem checked_midpoint_record
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (midRawIndex d q)=
      IntegralMixedChronologicalMidpointCode.code d (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (levelIndex q+1) :=
  IntegralMixedRoadmapMidpointRecord.checked_anchor_record h (levelIndex q) (checked_latest_lt hd)

theorem checked_midpoint_companion_record
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount d q) :
    WordList.get (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) (midRawIndex d q+1+i)=
      IntegralMixedChronologicalMidpointCode.code d (labels q) (producer false q) (producer true q)
        (levelIndex q+1) (d-i) :=
  IntegralMixedRoadmapCaptureRecords.checked_mid_record h (levelIndex q) i (checked_latest_lt hd) hi

theorem checked_midpoint_fit
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) :
    midRawIndex d q<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have H:=(h.2.2.2.2.1 (levelIndex q) (checked_latest_lt hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount midRawIndex at *
  omega

theorem checked_midpoint_companion_fit
    (h : IntegralMixedRoadmapChain.Checked d B sourceCap initial C (IntegralMixedRoadmapAtomic.payload q))
    (hd : 0<IntegralMixedRoadmapAtomic.depth q) (i : ℕ) (hi : i<captureCount d q) :
    midRawIndex d q+1+i<WordListRecords.count (IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapAtomic.payload q)) :=by
  have H:=(h.2.2.2.2.1 (levelIndex q) (checked_latest_lt hd)).2.2.1
  rw [IntegralMixedRoadmapChain.level_count] at H
  unfold IntegralMixedRoadmapChain.blockCount midRawIndex at *
  unfold captureCount at hi
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapProper

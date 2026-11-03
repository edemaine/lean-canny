/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicLayout
public import LeanCanny.Encoding.IntegralMixedRoadmapCaptureRecords
/-! # The complete latest atomic companion block has literal point records -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedChronologicalFrameCode.code

private theorem get_prefix (xs ys :List (List Bool)) (i :ℕ) (hi :i<xs.length) :
    WordList.get (WordList.encode (xs++ys)) i=WordList.get (WordList.encode xs) i:=by
  simp only [WordList.get_encode,List.getElem?_append_left hi]

theorem seed_capture_record (n B sourceCap initial C :ℕ) (q :List Bool)
    (h :IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q))
    (j :ℕ) (hj :j<n+1) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload q)) (1+j)=
      IntegralMixedChronologicalFrameCode.code n [] 0 (n-j) :=by
  rw [h.2.2.2.2.2.1]
  unfold IntegralMixedRoadmapChain.compiled IntegralMixedRoadmapChain.compiledCodes IntegralMixedRoadmapChain.meaningfulCodes
  simp only [List.append_assoc]
  rw [get_prefix _ _ (1+j) (by rw [IntegralMixedRoadmapChain.seedCodes_length];omega)]
  have H0 :WordListRecords.count ([] :List Bool)=0:=WordListRecords.count_encode []
  rw [show 1+j=j+1 by omega]
  simp only [IntegralMixedRoadmapChain.seedCodes,List.singleton_append,WordList.get_encode,
    List.getElem?_cons_succ,IntegralMixedChronologicalCompanionCode.codes,
    H0,Nat.sub_zero,List.getElem?_map,
    List.getElem?_range hj,Option.map_some,Option.getD_some]

theorem latest_capture_record {n B sourceCap initial C :ℕ} {q :List Bool}
    (h :IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q))
    (j :ℕ) (hj :j<free n q) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload q)) (first n initial q-initial+j)=
      IntegralMixedChronologicalFrameCode.code n (frozen q) (depth q) (n-j) :=by
  cases HD :depth q with
  | zero=>
    have HF :first n initial q=initial+1:=by unfold first;rw [seed_anchor n initial q HD]
    have HW :frozen q=[]:=by unfold frozen;rw [HD];rfl
    rw [HF,HW]
    have HJ :j<n+1:=by simpa only [free,HD,Nat.sub_zero] using hj
    simpa only [Nat.add_sub_cancel_left] using seed_capture_record n B sourceCap initial C q h j HJ
  | succ i=>
    have HI :i<IntegralMixedRoadmapChain.depth (payload q):=by change i<depth q;omega
    have HN :i<n:=by have H:=h.1;change depth q≤n at H;omega
    have HJ :j<n-i:=by unfold free at hj;omega
    have HR:=IntegralMixedRoadmapCaptureRecords.checked_child_record h i j HI HJ
    have HG :IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n (payload q) i)=n-i:=by
      simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
        IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k]
      omega
    have HC :IntegralMixedRoadmapLevel.freshLeft (IntegralMixedRoadmapChain.levelPacket n (payload q) i)+
        IntegralMixedRoadmapLevel.freshRight (IntegralMixedRoadmapChain.levelPacket n (payload q) i)=
        IntegralMixedRoadmapChain.freshCount (payload q) i:=by
      simp only [IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.freshRight,
        IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
        IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
        IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
      rfl
    have HB :first n initial q=initial+IntegralMixedRoadmapChain.rawStart n (payload q) i+
        IntegralMixedRoadmapChain.freshCount (payload q) i+2+(n-i):=by
      unfold first
      rw [child_anchor n initial q i HD HN]
      unfold IntegralMixedRoadmapLevel.childBirth IntegralMixedRoadmapLevel.afterEndpoints IntegralMixedRoadmapChain.birth
      rw [HG]
      omega
    have HW :IntegralMixedRoadmapChain.frozen (payload q) (i+1)=frozen q:=by unfold frozen;rw [HD]
    rw [HW] at HR
    rw [HB]
    convert HR using 1
    congr 1
    omega

theorem anchor_frame_good {n B sourceCap initial C :ℕ} {q :List Bool}
    (h :IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q)) :
    IntegralMixedChronologicalFrameCode.Good n (anchor n initial q) (frozen q) :=by
  cases HD :depth q with
  | zero=>
    have HW :frozen q=[]:=by unfold frozen;rw [HD];rfl
    rw [HW]
    exact (IntegralMixedRoadmapChain.seed_point_good _ _ 0 (by omega)).1
  | succ i=>
    have HI :i<IntegralMixedRoadmapChain.depth (payload q):=by change i<depth q;omega
    have HN :i<n:=by have H:=h.1;change depth q≤n at H;omega
    have HC:=IntegralMixedRoadmapLevel.child_frame_good (IntegralMixedRoadmapChain.level_checked h i HI).1
    rw [IntegralMixedRoadmapChain.level_frozen,←child_anchor n initial q i HD HN] at HC
    simpa only [frozen,HD] using HC

theorem capture_point_good {n B sourceCap initial C :ℕ} {q :List Bool}
    (h :IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q))
    (j :ℕ) (hj :j<free n q) :
    IntegralMixedChronologicalFrameCode.PointGood n (first n initial q+j) (frozen q) (depth q) (n-j) :=by
  have HD :depth q≤n:=h.1
  have HF:=IntegralMixedRoadmapLevel.frame_mono (anchor_frame_good h)
    (show anchor n initial q≤first n initial q+j by unfold first;omega)
  have HK:=frozen_count q
  refine ⟨HF,by omega,by omega,?_,by omega⟩
  unfold free at hj
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic

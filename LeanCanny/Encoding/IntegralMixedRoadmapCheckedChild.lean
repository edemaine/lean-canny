/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapAtomicCaptureRecords
/-! # The latest child anchor is critical from syntax checking alone -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapAtomic
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedChronologicalFrameCode.code

private theorem level_anchor_record (n : ℕ) (q : List Bool) :
    WordList.get (IntegralMixedRoadmapLevel.compiled n q)
      (IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+1+
        IntegralMixedRoadmapLevel.freeCount n q)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapLevel.childLabels q)
        (IntegralMixedRoadmapLevel.g q) (IntegralMixedRoadmapLevel.g q):=by
  let xs:=IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.left q) ++
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.right q) ++
    [IntegralMixedRoadmapLevel.midpointAnchor n q] ++
    IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
      (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q) (IntegralMixedRoadmapLevel.g q)
  have HX : xs.length=IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+1+
      IntegralMixedRoadmapLevel.freeCount n q:=by
    simp only [xs,List.length_append,List.length_singleton,IntegralMixedRoadmapEndpointSyntax.codes_length,
      IntegralMixedChronologicalMidpointCompanionCode.codes_length]
    unfold IntegralMixedRoadmapLevel.freshLeft IntegralMixedRoadmapLevel.freshRight
      IntegralMixedRoadmapLevel.freeCount IntegralMixedRoadmapLevel.g IntegralMixedRoadmapLevel.k
    omega
  have HC : IntegralMixedRoadmapLevel.codes n q=xs++([IntegralMixedRoadmapLevel.childAnchor n q]++
      IntegralMixedChronologicalCompanionCode.codes n (IntegralMixedRoadmapLevel.childLabels q) (IntegralMixedRoadmapLevel.g q)):=by
    simp only [xs,IntegralMixedRoadmapLevel.codes,List.append_assoc]
  rw [IntegralMixedRoadmapLevel.compiled,HC,←HX,WordList.get_encode,
    List.getElem?_append_right (Nat.le_refl _),Nat.sub_self,List.singleton_append,List.getElem?_cons_zero,Option.getD_some]
  rfl

private theorem checked_level_anchor {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i<IntegralMixedRoadmapChain.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw q)
      (IntegralMixedRoadmapChain.rawStart n q i+IntegralMixedRoadmapChain.freshCount q i+1+(n-i))=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q (i+1)) (i+1) (i+1):=by
  let lev:=IntegralMixedRoadmapChain.levelPacket n q i
  have HG : IntegralMixedRoadmapLevel.g lev=i+1:=by
    simp only [lev,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapChain.levelPacket,
      IntegralMixedRoadmapChain.withSlice_k]
  have HQ : IntegralMixedRoadmapLevel.freeCount n lev=n-i:=by
    unfold IntegralMixedRoadmapLevel.freeCount
    rw [HG]
    omega
  have HF : IntegralMixedRoadmapLevel.freshLeft lev+IntegralMixedRoadmapLevel.freshRight lev=
      IntegralMixedRoadmapChain.freshCount q i:=by
    simp only [lev,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.freshRight,
      IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapChain.levelPacket,
      IntegralMixedRoadmapChain.withSlice,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
    rfl
  have HI : IntegralMixedRoadmapLevel.freshLeft lev+IntegralMixedRoadmapLevel.freshRight lev+1+
      IntegralMixedRoadmapLevel.freeCount n lev<IntegralMixedRoadmapLevel.emittedCount n lev:=by
    unfold IntegralMixedRoadmapLevel.emittedCount
    omega
  have HR:=IntegralMixedRoadmapLevel.checked_raw_record (IntegralMixedRoadmapChain.level_checked h i hi)
    (h.2.2.2.2.1 i hi).2.2 _ HI
  rw [level_anchor_record,IntegralMixedRoadmapChain.level_frozen,HG,HQ,HF] at HR
  convert HR.symm using 1
  congr 1
  omega

theorem checked_anchor_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q)) (hd : 0<depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw (payload q)) (anchor n initial q-initial)=
      IntegralMixedChronologicalFrameCode.code n (frozen q) (depth q) (depth q):=by
  obtain ⟨i,HD⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have HI : i<IntegralMixedRoadmapChain.depth (payload q):=by change i<depth q;omega
  have HN : i<n:=by have H:=h.1;change depth q≤n at H;omega
  have HR:=checked_level_anchor h i HI
  have HG : IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n (payload q) i)=n-i:=by
    simp only [IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice_k]
    omega
  have HF : frozen q=IntegralMixedRoadmapChain.frozen (payload q) (i+1):=by unfold frozen;rw [HD]
  rw [HF,HD,child_anchor n initial q i HD HN]
  unfold IntegralMixedRoadmapLevel.childBirth IntegralMixedRoadmapLevel.afterEndpoints IntegralMixedRoadmapChain.birth
  rw [HG]
  have HC : IntegralMixedRoadmapLevel.freshLeft (IntegralMixedRoadmapChain.levelPacket n (payload q) i)+
      IntegralMixedRoadmapLevel.freshRight (IntegralMixedRoadmapChain.levelPacket n (payload q) i)=
      IntegralMixedRoadmapChain.freshCount (payload q) i:=by
    simp only [IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.freshRight,
      IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapChain.levelPacket,
      IntegralMixedRoadmapChain.withSlice,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
    rfl
  convert HR using 1
  congr 1
  omega

theorem anchor_point_good {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C (payload q)) :
    IntegralMixedChronologicalFrameCode.PointGood n (anchor n initial q) (frozen q) (depth q) (depth q):=by
  have HD : depth q≤n:=h.1
  have HC : WordListRecords.count (frozen q)≤depth q:=Nat.le_of_eq (frozen_count q)
  exact ⟨anchor_frame_good (q:=q) h,HC,Nat.lt_succ_of_le HD,HC,Nat.lt_succ_of_le HD⟩

end LeanCanny.Encoding.IntegralMixedRoadmapAtomic

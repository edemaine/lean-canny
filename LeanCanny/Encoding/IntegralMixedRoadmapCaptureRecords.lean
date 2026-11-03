/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode
/-! # Literal provenance of every midpoint and child companion

The lookup retains the original chronological producer labels. It makes
no inference about a physical point until that record's guards are used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapCaptureRecords
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedChronologicalFrameCode.code
  IntegralMixedChronologicalMidpointCode.code

private theorem get_middle (xs ys zs : List (List Bool)) (i : ℕ) (hi : i<ys.length) :
    WordList.get (WordList.encode ((xs++ys)++zs)) (xs.length+i)=
      WordList.get (WordList.encode ys) i :=by
  simp only [WordList.get_encode,List.append_assoc,
    List.getElem?_append_right (by omega : xs.length≤xs.length+i),Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]

theorem level_child_record (n : ℕ) (q : List Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapLevel.freeCount n q) :
    WordList.get (IntegralMixedRoadmapLevel.compiled n q)
      (IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+2+
        IntegralMixedRoadmapLevel.freeCount n q+i)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapLevel.childLabels q)
        (IntegralMixedRoadmapLevel.g q) (n-i) :=by
  let xs:=IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.left q) ++
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.right q) ++
    [IntegralMixedRoadmapLevel.midpointAnchor n q] ++
    IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
      (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q) (IntegralMixedRoadmapLevel.g q) ++
    [IntegralMixedRoadmapLevel.childAnchor n q]
  have HX : xs.length=IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+2+
      IntegralMixedRoadmapLevel.freeCount n q :=by
    simp only [xs,List.length_append,List.length_singleton,IntegralMixedRoadmapEndpointSyntax.codes_length,
      IntegralMixedChronologicalMidpointCompanionCode.codes_length]
    unfold IntegralMixedRoadmapLevel.freshLeft IntegralMixedRoadmapLevel.freshRight
      IntegralMixedRoadmapLevel.freeCount IntegralMixedRoadmapLevel.g IntegralMixedRoadmapLevel.k
    omega
  have HI : i<(IntegralMixedChronologicalCompanionCode.codes n (IntegralMixedRoadmapLevel.childLabels q)
      (IntegralMixedRoadmapLevel.g q)).length :=by
    simpa only [IntegralMixedChronologicalCompanionCode.codes,List.length_map,List.length_range,
      IntegralMixedRoadmapLevel.child_labels_count,IntegralMixedRoadmapLevel.freeCount,
      IntegralMixedRoadmapLevel.g] using hi
  have HC : IntegralMixedRoadmapLevel.codes n q=(xs++
      IntegralMixedChronologicalCompanionCode.codes n (IntegralMixedRoadmapLevel.childLabels q)
        (IntegralMixedRoadmapLevel.g q))++[] :=by simp only [xs,IntegralMixedRoadmapLevel.codes,List.append_nil]
  rw [IntegralMixedRoadmapLevel.compiled,HC,←HX,get_middle _ _ _ _ HI]
  have HI' : i<n+1-WordListRecords.count (IntegralMixedRoadmapLevel.childLabels q) :=by
    simpa only [IntegralMixedChronologicalCompanionCode.codes,List.length_map,List.length_range] using HI
  simp only [WordList.get_encode,IntegralMixedChronologicalCompanionCode.codes,
    List.getElem?_map,List.getElem?_range HI',Option.map_some,Option.getD_some]

theorem level_mid_record (n : ℕ) (q : List Bool) (i : ℕ)
    (hi : i<IntegralMixedRoadmapLevel.freeCount n q) :
    WordList.get (IntegralMixedRoadmapLevel.compiled n q)
      (IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+1+i)=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedRoadmapLevel.labels q)
        (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q)
        (IntegralMixedRoadmapLevel.g q) (n-i) :=by
  let xs:=IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.left q) ++
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.right q) ++
    [IntegralMixedRoadmapLevel.midpointAnchor n q]
  have HX : xs.length=IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q+1 :=by
    simp only [xs,List.length_append,List.length_singleton,IntegralMixedRoadmapEndpointSyntax.codes_length]
    rfl
  have HI : i<(IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
      (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q)
      (IntegralMixedRoadmapLevel.g q)).length :=by
    simpa only [IntegralMixedChronologicalMidpointCompanionCode.codes_length,
      IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k] using hi
  have HC : IntegralMixedRoadmapLevel.codes n q=(xs++
      IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
        (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q)
        (IntegralMixedRoadmapLevel.g q))++([IntegralMixedRoadmapLevel.childAnchor n q]++
          IntegralMixedChronologicalCompanionCode.codes n (IntegralMixedRoadmapLevel.childLabels q)
            (IntegralMixedRoadmapLevel.g q)) :=by simp only [xs,IntegralMixedRoadmapLevel.codes,List.append_assoc]
  rw [IntegralMixedRoadmapLevel.compiled,HC,←HX,get_middle _ _ _ _ HI]
  have HI' : i<n+1-(WordListRecords.count (IntegralMixedRoadmapLevel.labels q)+1) :=by
    simpa only [IntegralMixedChronologicalMidpointCompanionCode.codes_length] using HI
  simp only [WordList.get_encode,IntegralMixedChronologicalMidpointCompanionCode.codes,
    List.getElem?_map,List.getElem?_range HI',Option.map_some,Option.getD_some]

private theorem level_fields (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.labels (IntegralMixedRoadmapChain.levelPacket n q i)=IntegralMixedRoadmapChain.frozen q i ∧
    IntegralMixedRoadmapLevel.g (IntegralMixedRoadmapChain.levelPacket n q i)=i+1 ∧
    IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n q i)=n-i ∧
    IntegralMixedRoadmapLevel.freshLeft (IntegralMixedRoadmapChain.levelPacket n q i)+
      IntegralMixedRoadmapLevel.freshRight (IntegralMixedRoadmapChain.levelPacket n q i)=IntegralMixedRoadmapChain.freshCount q i :=by
  simp only [IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.freeCount,
    IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.freshRight,
    IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,IntegralMixedRoadmapLevel.packet,
    pairFst_pair,pairSnd_pair,IntegralMixedRoadmapChain.frozen_count,Nat.add_sub_add_right]
  exact ⟨True.intro,True.intro,True.intro,rfl⟩

theorem checked_child_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i j : ℕ) (hi : i<IntegralMixedRoadmapChain.depth q) (hj : j<n-i) :
    WordList.get (IntegralMixedRoadmapChain.raw q)
      (IntegralMixedRoadmapChain.rawStart n q i+IntegralMixedRoadmapChain.freshCount q i+2+(n-i)+j)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q (i+1)) (i+1) (n-j) :=by
  obtain ⟨_,HG,HQ,HF⟩:=level_fields n q i
  have HJ : j<IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n q i):=by rw [HQ];exact hj
  have HI : IntegralMixedRoadmapLevel.freshLeft (IntegralMixedRoadmapChain.levelPacket n q i)+
      IntegralMixedRoadmapLevel.freshRight (IntegralMixedRoadmapChain.levelPacket n q i)+2+
      IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n q i)+j<
      IntegralMixedRoadmapLevel.emittedCount n (IntegralMixedRoadmapChain.levelPacket n q i) :=by
    unfold IntegralMixedRoadmapLevel.emittedCount
    omega
  have HR:=IntegralMixedRoadmapLevel.checked_raw_record (IntegralMixedRoadmapChain.level_checked h i hi)
    (h.2.2.2.2.1 i hi).2.2 _ HI
  rw [level_child_record n _ j HJ,IntegralMixedRoadmapChain.level_frozen,HG,HQ,HF] at HR
  convert HR.symm using 1
  congr 1
  omega

theorem checked_mid_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i j : ℕ) (hi : i<IntegralMixedRoadmapChain.depth q) (hj : j<n-i) :
    WordList.get (IntegralMixedRoadmapChain.raw q)
      (IntegralMixedRoadmapChain.rawStart n q i+IntegralMixedRoadmapChain.freshCount q i+1+j)=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedRoadmapChain.frozen q i)
        (IntegralMixedRoadmapEndpointSyntax.field (IntegralMixedRoadmapChain.left q i) 1)
        (IntegralMixedRoadmapEndpointSyntax.field (IntegralMixedRoadmapChain.right q i) 1) (i+1) (n-j) :=by
  obtain ⟨HL,HG,HQ,HF⟩:=level_fields n q i
  have HJ : j<IntegralMixedRoadmapLevel.freeCount n (IntegralMixedRoadmapChain.levelPacket n q i):=by rw [HQ];exact hj
  have HI : IntegralMixedRoadmapLevel.freshLeft (IntegralMixedRoadmapChain.levelPacket n q i)+
      IntegralMixedRoadmapLevel.freshRight (IntegralMixedRoadmapChain.levelPacket n q i)+1+j<
      IntegralMixedRoadmapLevel.emittedCount n (IntegralMixedRoadmapChain.levelPacket n q i) :=by
    unfold IntegralMixedRoadmapLevel.emittedCount
    omega
  have HR:=IntegralMixedRoadmapLevel.checked_raw_record (IntegralMixedRoadmapChain.level_checked h i hi)
    (h.2.2.2.2.1 i hi).2.2 _ HI
  rw [level_mid_record n _ j HJ,HL,HG,HF] at HR
  have HP (r : Bool) : IntegralMixedRoadmapLevel.producer r (IntegralMixedRoadmapChain.levelPacket n q i)=
      IntegralMixedRoadmapEndpointSyntax.field (if r then IntegralMixedRoadmapChain.right q i else IntegralMixedRoadmapChain.left q i) 1 :=by
    cases r <;> simp only [IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.left,
      IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,ite_true]
  rw [HP false,HP true] at HR
  simp only [Bool.false_eq_true,ite_false,ite_true] at HR
  convert HR.symm using 1
  congr 1
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapCaptureRecords

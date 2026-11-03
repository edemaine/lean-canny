/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCaptureRecords
/-! # The checked midpoint anchor is the literal scale-two record -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapMidpointRecord
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedChronologicalMidpointCode.code

theorem level_anchor_record (n : ℕ) (q : List Bool) :
    WordList.get (IntegralMixedRoadmapLevel.compiled n q)
      (IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q)=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedRoadmapLevel.labels q)
        (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q)
        (IntegralMixedRoadmapLevel.g q) (IntegralMixedRoadmapLevel.g q) :=by
  let xs:=IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.left q)++
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.right q)
  have HL : xs.length=IntegralMixedRoadmapLevel.freshLeft q+IntegralMixedRoadmapLevel.freshRight q:=by
    simp only [xs,List.length_append,IntegralMixedRoadmapEndpointSyntax.codes_length]
    rfl
  have HC : IntegralMixedRoadmapLevel.codes n q=xs++
      [IntegralMixedRoadmapLevel.midpointAnchor n q]++
      IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
        (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q) (IntegralMixedRoadmapLevel.g q)++
      [IntegralMixedRoadmapLevel.childAnchor n q]++
      IntegralMixedChronologicalCompanionCode.codes n (IntegralMixedRoadmapLevel.childLabels q) (IntegralMixedRoadmapLevel.g q):=rfl
  rw [IntegralMixedRoadmapLevel.compiled,HC,←HL,WordList.get_encode]
  simp only [List.append_assoc,List.getElem?_append_right (le_refl xs.length),Nat.sub_self,
    List.cons_append,List.getElem?_cons_zero,Option.getD_some,IntegralMixedRoadmapLevel.midpointAnchor]

theorem checked_anchor_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i<IntegralMixedRoadmapChain.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw q)
      (IntegralMixedRoadmapChain.rawStart n q i+IntegralMixedRoadmapChain.freshCount q i)=
      IntegralMixedChronologicalMidpointCode.code n (IntegralMixedRoadmapChain.frozen q i)
        (IntegralMixedRoadmapEndpointSyntax.field (IntegralMixedRoadmapChain.left q i) 1)
        (IntegralMixedRoadmapEndpointSyntax.field (IntegralMixedRoadmapChain.right q i) 1) (i+1) (i+1) :=by
  let packet:=IntegralMixedRoadmapChain.levelPacket n q i
  have HF : IntegralMixedRoadmapLevel.freshLeft packet+IntegralMixedRoadmapLevel.freshRight packet=
      IntegralMixedRoadmapChain.freshCount q i:=by
    simp only [packet,IntegralMixedRoadmapLevel.freshLeft,IntegralMixedRoadmapLevel.freshRight,
      IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapChain.levelPacket,
      IntegralMixedRoadmapChain.withSlice,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair]
    rfl
  have HI : IntegralMixedRoadmapLevel.freshLeft packet+IntegralMixedRoadmapLevel.freshRight packet<
      IntegralMixedRoadmapLevel.emittedCount n packet:=by unfold IntegralMixedRoadmapLevel.emittedCount;omega
  have HR:=IntegralMixedRoadmapLevel.checked_raw_record (IntegralMixedRoadmapChain.level_checked h i hi)
    (h.2.2.2.2.1 i hi).2.2 _ HI
  rw [level_anchor_record,HF] at HR
  have HE : IntegralMixedRoadmapLevel.labels packet=IntegralMixedRoadmapChain.frozen q i ∧
      IntegralMixedRoadmapLevel.g packet=i+1:=by
    simp only [packet,IntegralMixedRoadmapLevel.labels,IntegralMixedRoadmapLevel.g,IntegralMixedRoadmapLevel.k,
      IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,IntegralMixedRoadmapLevel.packet,
      pairFst_pair,IntegralMixedRoadmapChain.frozen_count,and_self]
  have HP (r : Bool) : IntegralMixedRoadmapLevel.producer r packet=
      IntegralMixedRoadmapEndpointSyntax.field (if r then IntegralMixedRoadmapChain.right q i else IntegralMixedRoadmapChain.left q i) 1:=by
    cases r <;> simp only [packet,IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.left,
      IntegralMixedRoadmapLevel.right,IntegralMixedRoadmapChain.levelPacket,IntegralMixedRoadmapChain.withSlice,
      IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,Bool.false_eq_true,ite_false,ite_true]
  rw [HE.1,HE.2,HP false,HP true] at HR
  simpa only [Bool.false_eq_true,ite_false,ite_true] using HR.symm

end LeanCanny.Encoding.IntegralMixedRoadmapMidpointRecord

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainLedger
/-! # The last child capture is the next frame's own critical height

This is literal record provenance. It does not infer a critical point from
syntax alone: the creating record's physical guards are still required.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedChronologicalFrameCode.code

theorem companion_split_last (n : ℕ) (labels : List Bool) (g : ℕ)
    (hk : WordListRecords.count labels≤n) :
    ∃cs,IntegralMixedChronologicalCompanionCode.codes n labels g=
      cs++[IntegralMixedChronologicalFrameCode.code n labels g (WordListRecords.count labels)] :=by
  refine ⟨(List.range (n-WordListRecords.count labels)).map
    (fun i=>IntegralMixedChronologicalFrameCode.code n labels g (n-i)),?_⟩
  unfold IntegralMixedChronologicalCompanionCode.codes
  rw [show n+1-WordListRecords.count labels=(n-WordListRecords.count labels)+1 by omega,
    List.range_succ,List.map_append]
  simp only [List.map_cons,List.map_nil,Nat.sub_sub_self hk]

theorem level_split_last (n : ℕ) (q : List Bool) (hg : IntegralMixedRoadmapLevel.g q≤n) :
    ∃cs,IntegralMixedRoadmapLevel.codes n q=cs++
      [IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapLevel.childLabels q)
        (IntegralMixedRoadmapLevel.g q) (IntegralMixedRoadmapLevel.g q)] :=by
  have HK : WordListRecords.count (IntegralMixedRoadmapLevel.childLabels q)=IntegralMixedRoadmapLevel.g q:=by
    unfold IntegralMixedRoadmapLevel.childLabels IntegralMixedRoadmapLevel.g IntegralMixedRoadmapLevel.k
    exact IntegralMixedChronologicalEndpointCode.append_count _ _
  obtain ⟨cs,HC⟩:=companion_split_last n (IntegralMixedRoadmapLevel.childLabels q)
    (IntegralMixedRoadmapLevel.g q) (by rw [HK];exact hg)
  rw [HK] at HC
  refine ⟨IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.left q) ++
    IntegralMixedRoadmapEndpointSyntax.codes n (IntegralMixedRoadmapLevel.labels q) (IntegralMixedRoadmapLevel.right q) ++
    [IntegralMixedRoadmapLevel.midpointAnchor n q] ++
    IntegralMixedChronologicalMidpointCompanionCode.codes n (IntegralMixedRoadmapLevel.labels q)
      (IntegralMixedRoadmapLevel.producer false q) (IntegralMixedRoadmapLevel.producer true q) (IntegralMixedRoadmapLevel.g q) ++
    [IntegralMixedRoadmapLevel.childAnchor n q] ++cs,?_⟩
  simp only [IntegralMixedRoadmapLevel.codes,HC,List.append_assoc]

private theorem get_final (cs : List (List Bool)) (last : List Bool) :
    WordList.get (WordList.encode (cs++[last])) cs.length=last :=by
  rw [WordList.get_encode]
  simp

theorem level_final (n : ℕ) (q : List Bool) (hg : IntegralMixedRoadmapLevel.g q≤n) :
    WordList.get (IntegralMixedRoadmapLevel.compiled n q) (IntegralMixedRoadmapLevel.emittedCount n q-1)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapLevel.childLabels q)
        (IntegralMixedRoadmapLevel.g q) (IntegralMixedRoadmapLevel.g q) :=by
  obtain ⟨cs,HC⟩:=level_split_last n q hg
  have HL:=congrArg List.length HC
  rw [IntegralMixedRoadmapLevel.codes_length,List.length_append,List.length_singleton] at HL
  change IntegralMixedRoadmapLevel.emittedCount n q=cs.length+1 at HL
  rw [IntegralMixedRoadmapLevel.compiled,HC,show IntegralMixedRoadmapLevel.emittedCount n q-1=cs.length by omega]
  exact get_final _ _

theorem checked_next_height_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i<IntegralMixedRoadmapChain.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw q) (IntegralMixedRoadmapChain.rawStart n q (i+1)-1)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q (i+1)) (i+1) (i+1) :=by
  have HG : IntegralMixedRoadmapLevel.g (IntegralMixedRoadmapChain.levelPacket n q i)=i+1:=by
    unfold IntegralMixedRoadmapLevel.g IntegralMixedRoadmapChain.levelPacket
    rw [IntegralMixedRoadmapChain.withSlice_k]
  have HGn : IntegralMixedRoadmapLevel.g (IntegralMixedRoadmapChain.levelPacket n q i)≤n:=by
    rw [HG]
    have HD:=h.1
    omega
  have HP : 0<IntegralMixedRoadmapLevel.emittedCount n (IntegralMixedRoadmapChain.levelPacket n q i):=by
    unfold IntegralMixedRoadmapLevel.emittedCount
    omega
  have HR:=IntegralMixedRoadmapLevel.checked_raw_record
    (IntegralMixedRoadmapChain.level_checked h i hi) (h.2.2.2.2.1 i hi).2.2
    (IntegralMixedRoadmapLevel.emittedCount n (IntegralMixedRoadmapChain.levelPacket n q i)-1) (by omega)
  rw [level_final n _ HGn,IntegralMixedRoadmapChain.level_frozen n q i,HG,
    IntegralMixedRoadmapChain.level_count] at HR
  have HB : 0<IntegralMixedRoadmapChain.blockCount n q i:=by
    rw [←IntegralMixedRoadmapChain.level_count n q i]
    exact HP
  rw [IntegralMixedRoadmapChain.rawStart_succ]
  convert HR.symm using 1
  congr 1
  omega

private theorem get_prefix (xs ys : List (List Bool)) (i : ℕ) (hi : i<xs.length) :
    WordList.get (WordList.encode (xs++ys)) i=WordList.get (WordList.encode xs) i :=by
  simp only [WordList.get_encode,List.getElem?_append_left hi]

theorem seed_final (n : ℕ) :
    WordList.get (WordList.encode (IntegralMixedRoadmapChain.seedCodes n)) (n+1)=
      IntegralMixedChronologicalFrameCode.code n [] 0 0 :=by
  have HN : WordListRecords.count ([] : List Bool)=0:=WordListRecords.count_encode []
  obtain ⟨cs,HC⟩:=companion_split_last n [] 0 (by rw [HN];omega)
  rw [HN] at HC
  have HS : IntegralMixedRoadmapChain.seedCodes n=
      ([IntegralMixedRoadmapChain.seedCode n]++cs)++[IntegralMixedChronologicalFrameCode.code n [] 0 0]:=by
    simp only [IntegralMixedRoadmapChain.seedCodes,HC,List.append_assoc]
  have HL:=congrArg List.length HS
  rw [IntegralMixedRoadmapChain.seedCodes_length,List.length_append,List.length_append,
    List.length_singleton,List.length_singleton] at HL
  rw [HS,show n+1=([IntegralMixedRoadmapChain.seedCode n]++cs).length by simp only [List.length_append,List.length_singleton];omega]
  exact get_final _ _

theorem checked_initial_height_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q) :
    WordList.get (IntegralMixedRoadmapChain.raw q) (IntegralMixedRoadmapChain.rawStart n q 0-1)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q 0) 0 0 :=by
  have HS : IntegralMixedRoadmapChain.rawStart n q 0=n+2:=by
    simp only [IntegralMixedRoadmapChain.rawStart,IntegralMixedRoadmapChain.prefixCount,
      Finset.sum_range_zero,add_zero]
  have HF : IntegralMixedRoadmapChain.frozen q 0=[]:=rfl
  rw [HS,HF,show n+2-1=n+1 by omega,h.2.2.2.2.2.1]
  unfold IntegralMixedRoadmapChain.compiled IntegralMixedRoadmapChain.compiledCodes
    IntegralMixedRoadmapChain.meaningfulCodes
  simp only [List.append_assoc]
  rw [get_prefix _ _ (n+1) (by rw [IntegralMixedRoadmapChain.seedCodes_length];omega)]
  exact seed_final n

theorem checked_own_height_record {n B sourceCap initial C : ℕ} {q : List Bool}
    (h : IntegralMixedRoadmapChain.Checked n B sourceCap initial C q)
    (i : ℕ) (hi : i≤IntegralMixedRoadmapChain.depth q) :
    WordList.get (IntegralMixedRoadmapChain.raw q) (IntegralMixedRoadmapChain.rawStart n q i-1)=
      IntegralMixedChronologicalFrameCode.code n (IntegralMixedRoadmapChain.frozen q i) i i :=by
  cases i with
  | zero=>exact checked_initial_height_record h
  | succ i=>exact checked_next_height_record h i (by omega)

end LeanCanny.Encoding.IntegralMixedRoadmapOwnHeightCode

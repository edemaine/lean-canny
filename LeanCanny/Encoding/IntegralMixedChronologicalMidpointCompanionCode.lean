/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointActual
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointSignature
public import LeanCanny.Geometry.IntegralMixedPointCompanionCodeStable
/-! # Native companions in the actual scale-two midpoint frame

Chronological coordinates decrease from n to k+1. The objective, original
frozen labels and both endpoint producer labels stay fixed in every code.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointCompanionCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFrozenFrame IntegralMixedPointCompanion IntegralMixedChronologicalMidpointSignature
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def codes (n : ℕ) (labels : List Bool) (a b g : ℕ):=
  (List.range (n+1-(WordListRecords.count labels+1))).map
    (fun i=>IntegralMixedChronologicalMidpointCode.code n labels a b g (n-i))
def word (n : ℕ) (labels : List Bool) (a b g : ℕ):=WordList.encode (codes n labels a b g)

theorem codes_length (n : ℕ) (labels : List Bool) (a b g : ℕ) :
    (codes n labels a b g).length=n+1-(WordListRecords.count labels+1) :=by
  simp only [codes,List.length_map,List.length_range]

theorem word_FP {n a b g : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (ha : BinaryFn a) (hb : BinaryFn b) (hg : BinaryFn g) (hw : labels∈FP) :
    (fun q=>word (n q) (labels q) (a q) (b q) (g q))∈FP :=by
  have HN:=hn.comp pairFst_mem_FP
  have HJ:=(BinaryFn.ofUnary HN).sub (BinaryFn.ofUnary UnaryFn.index)
  have HC:=IntegralMixedChronologicalMidpointCode.code_FP HN (ha.comp pairFst_mem_FP)
    (hb.comp pairFst_mem_FP) (hg.comp pairFst_mem_FP) HJ (mem_FP_comp pairFst_mem_FP hw)
  have HQ:=(hn.add (UnaryFn.const 1)).sub ((WordListRecords.count_unary.comp hw).add (UnaryFn.const 1))
  apply mem_FP_of_eq (flatMap_range_mem_FP (mem_FP_pair HC (constFn_mem_FP [])) (HQ.replicate_mem_FP true))
  intro q
  simp only [word,codes,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate]

private theorem codes_map {n birth : ℕ} (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→IntegralMixedCausalRowConstructor.Row birth) (g : Free frozen) (js : List (Free frozen)) :
    IntegralMixedPointCompanion.codes frozen double rows g js=
      js.map (fun j=>(pointData frozen double rows g 0 j).code) :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>rw [IntegralMixedPointCompanion.codes,List.map_cons,pointData_code_stable,ih]

theorem codes_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth)
    (g : Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (IntegralMixedPointCompanion.codes (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g (orderedFree d hk a b)).reverse=
      codes n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val :=by
  have HD (j : Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
      (pointData (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
        (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
        g 0 j).code=IntegralMixedChronologicalMidpointCode.code n
          (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val j.val.val :=
    IntegralMixedChronologicalMidpointCode.data_code d hk a b g.val j.val g.property j.property
  rw [codes_map,←List.map_reverse]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_reverse,orderedFree_length,codes,
      IntegralMixedChronologicalFrameCode.labels_count,List.length_range,freeCount]
  · intro i hi hj
    simp only [List.length_map,List.length_reverse,orderedFree_length] at hi
    have HI : i<(orderedFree d hk a b).length:=by rw [orderedFree_length];exact hi
    simp only [List.getElem_map,List.getElem_reverse,HD,codes,List.getElem_range]
    apply congrArg (IntegralMixedChronologicalMidpointCode.code n
      (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val)
    have HE:=orderedFree_get d hk a b ⟨(orderedFree d hk a b).length-1-i,by omega⟩
    simp only [List.get_eq_getElem] at HE
    rw [HE,orderedFree_length]
    unfold freeCount at *
    omega

theorem word_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth)
    (g : Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    WordList.encode ((IntegralMixedPointCompanion.codes (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen
      (midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)) (IntegralMixedChronologicalMidpoint.rows d hk a b)
      g (orderedFree d hk a b)).reverse)=
      word n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val :=
  congrArg WordList.encode (codes_actual d hk a b g)

def wordBound (n birth : ℕ):=(2*IntegralMixedCutRecordConstructor.codeBudget n birth 0+2)*(n+1)

theorem word_size {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth)
    (g : Free (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (word n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val).length≤wordBound n birth :=by
  have HC : ∀w∈codes n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val,
      w.length≤IntegralMixedCutRecordConstructor.codeBudget n birth 0:=by
    intro w hw
    rw [←codes_actual d hk a b g,List.mem_reverse,codes_map] at hw
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hw
    exact (pointData _ _ _ g 0 j).code_length.trans (IntegralMixedCutRecordConstructor.critical_codeBudget_le n birth 0)
  have H:=WordList.length_le _ _ HC
  have HL : (codes n (IntegralMixedChronologicalFrameCode.labels d) a.val b.val g.val.val).length≤n+1:=by
    rw [codes_length]
    exact Nat.sub_le _ _
  exact H.trans (Nat.mul_le_mul_left _ HL)

theorem wordBound_unary {n birth : List Bool→ℕ} (hn : UnaryFn n) (hb : BinaryFn birth) :
    UnaryFn (fun q=>wordBound (n q) (birth q)) :=by
  have HC:=IntegralMixedCutRecordConstructor.codeBudget_unary hn hb (UnaryFn.const 0)
  exact (((UnaryFn.const 2).mul HC).add (UnaryFn.const 2)).mul (hn.add (UnaryFn.const 1))

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointCompanionCode

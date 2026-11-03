/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
public import LeanCanny.Geometry.IntegralMixedChronologicalPointSignature
public import LeanCanny.Geometry.IntegralMixedPointCompanionCodeStable
/-! # Native chronological compilation of all free-coordinate companions

The physical coordinates occur in decreasing order in the chronological
word, matching the actual newest-first interpreter. Retention changes the
command's references and current Q but preserves every emitted record byte.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCompanionCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralMixedHistory
open IntegralMixedFrozenFrame IntegralMixedPointCompanion
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def codes (n : ℕ) (labels : List Bool) (g : ℕ) :=
  (List.range (n+1-WordListRecords.count labels)).map
    (fun i=>IntegralMixedChronologicalFrameCode.code n labels g (n-i))
def word (n : ℕ) (labels : List Bool) (g : ℕ) :=WordList.encode (codes n labels g)

theorem word_FP {n g : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hg : BinaryFn g) (hw : labels∈FP) :
    (fun q=>word (n q) (labels q) (g q))∈FP :=by
  have HN : UnaryFn (fun p=>n (pairFst p)):=hn.comp pairFst_mem_FP
  have HG : BinaryFn (fun p=>g (pairFst p)):=hg.comp pairFst_mem_FP
  have HJ:=(BinaryFn.ofUnary HN).sub (BinaryFn.ofUnary UnaryFn.index)
  have HC:=IntegralMixedChronologicalFrameCode.code_FP HN HG HJ (mem_FP_comp pairFst_mem_FP hw)
  have HQ:=(hn.add (UnaryFn.const 1)).sub (WordListRecords.count_unary.comp hw)
  apply mem_FP_of_eq (flatMap_range_mem_FP (mem_FP_pair HC (constFn_mem_FP [])) (HQ.replicate_mem_FP true))
  intro q
  simp only [word,codes,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate]

private theorem codes_map {n birth : ℕ} (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→IntegralMixedCausalRowConstructor.Row birth) (g : Free frozen)
    (js : List (Free frozen)) :
    IntegralMixedPointCompanion.codes frozen double rows g js=
      js.map (fun j=>(pointData frozen double rows g 0 j).code) :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    rw [IntegralMixedPointCompanion.codes,List.map_cons,pointData_code_stable,ih]

theorem codes_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g : Free d.frame.frozen) :
    (IntegralMixedPointCompanion.codes d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i))
      g d.orderedFree).reverse=codes n (IntegralMixedChronologicalFrameCode.labels d) g.val.val :=by
  have HD (j : Free d.frame.frozen) :
      (pointData d.frame.frozen (fun _=>false) (fun i=>.single (d.atom i)) g 0 j).code=
        IntegralMixedChronologicalFrameCode.code n (IntegralMixedChronologicalFrameCode.labels d) g.val.val j.val.val :=
    IntegralMixedChronologicalFrameCode.data_code d g.val j.val g.property j.property
  rw [codes_map,←List.map_reverse]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_reverse,d.orderedFree_length,codes,
      IntegralMixedChronologicalFrameCode.labels_count,List.length_range,
      IntegralMixedChronologicalFrame.Descriptor.freeCount]
  · intro i hi hj
    simp only [List.length_map,List.length_reverse,d.orderedFree_length] at hi
    have HI : i<d.orderedFree.length:=by rw [d.orderedFree_length];exact hi
    simp only [List.getElem_map,List.getElem_reverse,HD,codes,List.getElem_range]
    apply congrArg (IntegralMixedChronologicalFrameCode.code n (IntegralMixedChronologicalFrameCode.labels d) g.val.val)
    have HE:=d.orderedFree_get ⟨d.orderedFree.length-1-i,by omega⟩
    simp only [List.get_eq_getElem] at HE
    rw [HE,d.orderedFree_length]
    have HK:=d.length_le
    unfold IntegralMixedChronologicalFrame.Descriptor.freeCount at *
    omega

theorem word_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (g : Free d.frame.frozen) :
    WordList.encode ((IntegralMixedPointCompanion.codes d.frame.frozen (fun _=>false)
      (fun i=>.single (d.atom i)) g d.orderedFree).reverse)=
      word n (IntegralMixedChronologicalFrameCode.labels d) g.val.val :=
  congrArg WordList.encode (codes_actual d g)

end LeanCanny.Encoding.IntegralMixedChronologicalCompanionCode

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
public import LeanCanny.Encoding.IntegralMixedCutRecordBounds
/-! # Native sweep cut words from chronological prefix labels

The first free coordinate is the swept height. The temporary frame has one
more frozen slot, with no retained height alias. Current Q is selected by
the existing cut ABI. The stored factor choice and degree are input bits,
not computations of a specialized polynomial's degree.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalCutCode
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

def emptyRows (n : ℕ) :=WordList.encode (List.replicate (n+1) ([] : List Bool))

theorem emptyRows_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun q=>emptyRows (n q))∈FP :=by
  apply mem_FP_of_eq (flatMap_range_mem_FP (constFn_mem_FP (pair [] []))
    ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [emptyRows,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_replicate,List.length_replicate]
  have HE (xs : List ℕ) : xs.flatMap (fun _=>pair [] [])=(List.replicate xs.length (pair [] [])).flatten:=by
    induction xs with
    | nil=>rfl
    | cons a xs ih=>
      simpa only [List.flatMap_cons,List.length_cons,List.replicate_succ,List.flatten_cons] using congrArg ((pair [] [])++·) ih
  simpa only [List.length_range] using HE (List.range (n q+1))

def code (n : ℕ) (labels : List Bool) (g j tag choice degree : ℕ) :=
  IntegralMixedCausalRecordDegree.withDegree
    (IntegralMixedCutRecordConstructor.word (WordListRecords.count labels+1)
      (g-(WordListRecords.count labels+1)) (j-(WordListRecords.count labels+1))
      (WordListRecords.count labels) tag choice (IntegralMixedChronologicalFrameCode.rows n labels)
      (emptyRows n) (List.replicate (n+1) false) true) degree

theorem code_FP {n g j tag choice degree : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hg : BinaryFn g) (hj : BinaryFn j) (ht : BinaryFn tag)
    (hc : BinaryFn choice) (hd : BinaryFn degree) (hw : labels∈FP) :
    (fun q=>code (n q) (labels q) (g q) (j q) (tag q) (choice q) (degree q))∈FP :=by
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)
  have HS:=HK.add (BinaryFn.const 1)
  exact IntegralMixedCausalRecordDegree.withDegree_FP
    (IntegralMixedCutRecordConstructor.word_FP HS (hg.sub HS) (hj.sub HS) HK ht hc
      (IntegralMixedChronologicalFrameCode.rows_FP hn hw) (emptyRows_FP hn)
      ((hn.add (UnaryFn.const 1)).replicate_mem_FP false) (constFn_mem_FP [true])) hd

def Good (n birth : ℕ) (labels : List Bool) (g j : ℕ) :=
  IntegralMixedChronologicalFrameCode.Good n birth labels ∧ WordListRecords.count labels+1≤g ∧
    g<n+1 ∧ WordListRecords.count labels+1≤j ∧ j<n+1

theorem good_FP {n birth g j : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (hg : BinaryFn g) (hj : BinaryFn j) (hw : labels∈FP) :
    FPPred (fun q=>Good (n q) (birth q) (labels q) (g q) (j q)) :=by
  have HK:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)).add (BinaryFn.const 1)
  have HN:=(BinaryFn.ofUnary hn).add (BinaryFn.const 1)
  exact (IntegralMixedChronologicalFrameCode.good_FP hn hb hw).and
    ((HK.le hg).and ((hg.lt HN).and ((HK.le hj).and (hj.lt HN))))

end LeanCanny.Encoding.IntegralMixedChronologicalCutCode

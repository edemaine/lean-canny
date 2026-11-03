/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
public import LeanCanny.Encoding.IntegralMixedCutRecordBounds
/-! # Native mean-centered cut ABI with two original endpoint producers

No mean scalar, bank denominator or sampler word is serialized.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical

def code (n : ℕ) (labels : List Bool) (a b g j tag choice degree : ℕ):=
  IntegralMixedCausalRecordDegree.withDegree
    (IntegralMixedCutRecordConstructor.word (WordListRecords.count labels+1)
      (g-(WordListRecords.count labels+1)) (j-(WordListRecords.count labels+1))
      (WordListRecords.count labels) tag choice
      (IntegralMixedChronologicalFrameCode.rows n labels)
      (IntegralMixedChronologicalMidpointCode.midRows n labels a b)
      (IntegralMixedChronologicalMidpointCode.doubles n labels) true) degree

theorem code_FP {n a b g j tag choice degree : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (ha : BinaryFn a) (hb : BinaryFn b) (hg : BinaryFn g) (hj : BinaryFn j)
    (ht : BinaryFn tag) (hc : BinaryFn choice) (hd : BinaryFn degree) (hw : labels∈FP) :
    (fun q=>code (n q) (labels q) (a q) (b q) (g q) (j q) (tag q) (choice q) (degree q))∈FP:=by
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)
  have HS:=HK.add (BinaryFn.const 1)
  exact IntegralMixedCausalRecordDegree.withDegree_FP
    (IntegralMixedCutRecordConstructor.word_FP HS (hg.sub HS) (hj.sub HS) HK ht hc
      (IntegralMixedChronologicalFrameCode.rows_FP hn hw)
      (IntegralMixedChronologicalMidpointCode.midRows_FP hn ha hb hw)
      (IntegralMixedChronologicalMidpointCode.doubles_FP hn hw) (constFn_mem_FP [true])) hd

end LeanCanny.Encoding.IntegralMixedChronologicalMeanCutCode

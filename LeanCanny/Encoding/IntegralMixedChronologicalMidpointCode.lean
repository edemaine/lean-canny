/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
/-! # Native midpoint point records depend only on chronological labels

The original frozen-row table is unchanged. One sum-row and one double bit
freeze its first free coordinate at the mean of two retained endpoints.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedCriticalRecordConstructor
open IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def producerWord (a : ℕ):=pair [true] (BinaryNatCode.encode a)
def midRow (labels : List Bool) (a b i : ℕ):=
  if i=WordListRecords.count labels then sumWord (producerWord a) (producerWord b) else []
def midRows (n : ℕ) (labels : List Bool) (a b : ℕ):=
  WordList.encode ((List.range (n+1)).map (midRow labels a b))
def doubles (n : ℕ) (labels : List Bool):=
  (List.range (n+1)).map (fun i=>decide (i=WordListRecords.count labels))
def code (n : ℕ) (labels : List Bool) (a b g j : ℕ):=
  word (WordListRecords.count labels+1) (g-(WordListRecords.count labels+1))
    (j-(WordListRecords.count labels+1)) (IntegralMixedChronologicalFrameCode.rows n labels)
    (midRows n labels a b) (doubles n labels)

theorem producerWord_FP {a : List Bool→ℕ} (ha : BinaryFn a) :
    (fun q=>producerWord (a q))∈FP:=mem_FP_pair (constFn_mem_FP [true]) ha.bits_mem_FP

theorem midRows_FP {n a b : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (ha : BinaryFn a) (hb : BinaryFn b) (hw : labels∈FP) :
    (fun q=>midRows (n q) (labels q) (a q) (b q))∈FP :=by
  have HK:=WordListRecords.count_unary.comp (mem_FP_comp pairFst_mem_FP hw)
  have HG:=(BinaryFn.ofUnary UnaryFn.index).eq (BinaryFn.ofUnary HK)
  have HS:=sumWord_FP (producerWord_FP ha) (producerWord_FP hb)
  have HE:=(mem_FP_pair (HG.ite_mem_FP (mem_FP_comp pairFst_mem_FP HS) (constFn_mem_FP []))
    (constFn_mem_FP []))
  apply mem_FP_of_eq (flatMap_range_mem_FP HE ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [midRows,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,midRow]

theorem doubles_FP {n : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hw : labels∈FP) : (fun q=>doubles (n q) (labels q))∈FP :=by
  have HK:=WordListRecords.count_unary.comp (mem_FP_comp pairFst_mem_FP hw)
  have HG:=(BinaryFn.ofUnary UnaryFn.index).eq (BinaryFn.ofUnary HK)
  unfold doubles
  apply bitwise_mem_FP ((hn.add (UnaryFn.const 1)).replicate_mem_FP true) HG.flag_mem_FP
  intro q i
  simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem code_FP {n a b g j : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (ha : BinaryFn a) (hb : BinaryFn b) (hg : BinaryFn g) (hj : BinaryFn j)
    (hw : labels∈FP) : (fun q=>code (n q) (labels q) (a q) (b q) (g q) (j q))∈FP :=by
  have HK:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)).add (BinaryFn.const 1)
  exact word_FP HK (hg.sub HK) (hj.sub HK) (IntegralMixedChronologicalFrameCode.rows_FP hn hw)
    (midRows_FP hn ha hb hw) (doubles_FP hn hw)

def Good (n birth : ℕ) (labels : List Bool) (a b g j : ℕ) : Prop :=
  IntegralMixedChronologicalFrameCode.Good n birth labels ∧ a<birth ∧ b<birth ∧
    WordListRecords.count labels+1≤g ∧ g<n+1 ∧ WordListRecords.count labels+1≤j ∧ j<n+1

theorem good_FP {n birth a b g j : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hm : BinaryFn birth) (ha : BinaryFn a) (hb : BinaryFn b)
    (hg : BinaryFn g) (hj : BinaryFn j) (hw : labels∈FP) :
    FPPred (fun q=>Good (n q) (birth q) (labels q) (a q) (b q) (g q) (j q)) :=by
  have HK:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)).add (BinaryFn.const 1)
  have HN:=(BinaryFn.ofUnary hn).add (BinaryFn.const 1)
  exact (IntegralMixedChronologicalFrameCode.good_FP hn hm hw).and
    ((ha.lt hm).and ((hb.lt hm).and ((HK.le hg).and ((hg.lt HN).and ((HK.le hj).and (hj.lt HN))))))

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointCode

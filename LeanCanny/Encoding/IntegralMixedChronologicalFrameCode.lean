/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameRetained
public import LeanCanny.Encoding.WordListRecords
public import LeanCanny.Encoding.IntegralMixedCriticalRecordBounds
/-! # Native original critical records from chronological frame labels

Only the producer labels, physical dimension and selected coordinates are
read. No current denominator, interpreted point or sampler word is encoded.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalFrameCode
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedCriticalRecordConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def row (labels : List Bool) (i : ℕ) :=
  if i<WordListRecords.count labels then
    pair [true] (BinaryNatCode.encode (Nat.fromBitsLE (WordList.get labels i))) else []

def entry (p : List Bool) :=pair (row (pairFst p) (pairSnd p).length) []

theorem entry_FP : entry∈FP :=by
  have HP:=mem_FP_comp WordListRecords.indexPacket_FP WordList.reader_FP
  have HI:=UnaryFn.index
  have HC:=WordListRecords.count_unary.comp pairFst_mem_FP
  have HB:=((BinaryFn.ofUnary HI).lt (BinaryFn.ofUnary HC)).ite_mem_FP
    (mem_FP_pair (constFn_mem_FP [true]) (BinaryFn.fromBits HP).bits_mem_FP) (constFn_mem_FP [])
  exact mem_FP_of_eq (mem_FP_pair HB (constFn_mem_FP [])) (fun p=>by
    simp only [entry,row,Function.comp_apply,WordListRecords.indexPacket,WordList.reader,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])

def rows (n : ℕ) (labels : List Bool) :=
  WordList.encode ((List.range (n+1)).map (row labels))

theorem rows_FP {n : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hw : labels∈FP) : (fun q=>rows (n q) (labels q))∈FP :=by
  have Hpacket : (fun p=>pair (labels (pairFst p)) (pairSnd p))∈FP:=
    mem_FP_pair (mem_FP_comp pairFst_mem_FP hw) pairSnd_mem_FP
  have HE:=mem_FP_comp Hpacket entry_FP
  apply mem_FP_of_eq (flatMap_range_mem_FP HE ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [rows,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,entry,pairFst_pair,pairSnd_pair,List.length_replicate]

def code (n : ℕ) (labels : List Bool) (g j : ℕ) :=
  word (WordListRecords.count labels) (g-WordListRecords.count labels) (j-WordListRecords.count labels)
    (rows n labels) (WordList.encode (List.replicate (n+1) [])) (List.replicate (n+1) false)

theorem code_FP {n g j : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hg : BinaryFn g) (hj : BinaryFn j) (hw : labels∈FP) :
    (fun q=>code (n q) (labels q) (g q) (j q))∈FP :=by
  have HK:=WordListRecords.count_unary.comp hw
  have HM : (fun q=>WordList.encode (List.replicate (n q+1) []))∈FP:=by
    apply mem_FP_of_eq (flatMap_range_mem_FP (constFn_mem_FP (pair [] []))
      ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
    intro q
    simp only [FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_replicate,List.length_replicate]
    have HE (xs : List ℕ) : xs.flatMap (fun _=>pair [] [])=
        (List.replicate xs.length (pair [] [])).flatten:=by
      induction xs with
      | nil=>rfl
      | cons a xs ih=>
        simpa only [List.flatMap_cons,List.length_cons,List.replicate_succ,List.flatten_cons] using
          congrArg ((pair [] [])++·) ih
    simpa only [List.length_range] using HE (List.range (n q+1))
  exact word_FP (BinaryFn.ofUnary HK) (hg.sub (BinaryFn.ofUnary HK)) (hj.sub (BinaryFn.ofUnary HK))
    (rows_FP hn hw) HM ((hn.add (UnaryFn.const 1)).replicate_mem_FP false)

def Good (n birth : ℕ) (labels : List Bool) : Prop :=
  WordListRecords.count labels≤n+1 ∧
    ∀ i<WordListRecords.count labels,Nat.fromBitsLE (WordList.get labels i)<birth

theorem good_FP {n birth : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (hw : labels∈FP) :
    FPPred (fun q=>Good (n q) (birth q) (labels q)) :=by
  have HK:=WordListRecords.count_unary.comp hw
  have Hlookup : (fun p=>WordList.get (labels (pairFst p)) (pairSnd p).length)∈FP:=by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hw)
      (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP)
    intro p
    simp only [WordList.reader,Function.comp_apply,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have Hguard:=(BinaryFn.fromBits Hlookup).lt (hb.comp pairFst_mem_FP)
  exact (((BinaryFn.ofUnary HK).le (BinaryFn.ofUnary (hn.add (UnaryFn.const 1)))).and
    (Hguard.forall_lt HK)).of_iff (fun q=>by
      simp only [Good,Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate])

end LeanCanny.Encoding.IntegralMixedChronologicalFrameCode

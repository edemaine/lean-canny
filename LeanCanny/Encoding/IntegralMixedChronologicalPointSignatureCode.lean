/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalPointSignature
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
/-! # A polynomial-time writer for the complete physical point signature

It uses the frozen producer list and the fixed ordered companion layout.
Every emitted label is chronological, so a later padding suffix leaves it
unchanged. No sample word, root value or denominator is an input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalPointSignatureCode
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open scoped Classical

def producer (n birth : ℕ) (labels : List Bool) (i : ℕ) :=
  if i<WordListRecords.count labels then Nat.fromBitsLE (WordList.get labels i)
  else birth+(n+1-WordListRecords.count labels)-1-(i-WordListRecords.count labels)

def code (n birth : ℕ) (labels : List Bool) :=
  WordList.encode ((List.range (n+1)).map (fun i=>BinaryNatCode.encode (producer n birth labels i)))

theorem code_FP {n birth : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (hw : labels∈FP) :
    (fun q=>code (n q) (birth q) (labels q))∈FP :=by
  have HW:=mem_FP_comp pairFst_mem_FP hw
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp HW)
  have HI:=BinaryFn.ofUnary UnaryFn.index
  have Hread:=mem_FP_comp (mem_FP_pair HW HI.bits_mem_FP) WordList.reader_FP
  have HB : BinaryFn (fun p=>birth (pairFst p)):=hb.comp pairFst_mem_FP
  have HN : BinaryFn (fun p=>n (pairFst p)):= (BinaryFn.ofUnary hn).comp pairFst_mem_FP
  have Htail:=(HB.add (HN.add (BinaryFn.const 1) |>.sub HK))
    |>.sub (BinaryFn.const 1) |>.sub (HI.sub HK)
  have HP:=BinaryFn.ite (HI.lt HK) (BinaryFn.fromBits Hread) Htail
  have HE:=mem_FP_pair HP.bits_mem_FP (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [code,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,WordList.reader,
    BinaryNatCode.encode,Nat.fromBitsLE_bits,producer]

theorem producer_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (i : Fin (n+1)) :
    producer n birth (IntegralMixedChronologicalFrameCode.labels d) i.val=(d.pointProducer i).val :=by
  unfold producer
  rw [IntegralMixedChronologicalFrameCode.labels_count]
  split_ifs with hi
  · rw [IntegralMixedChronologicalFrameCode.labels_lookup d i.val hi]
    simp only [IntegralMixedChronologicalFrame.Descriptor.pointProducer,dite_eq_left hi]
  · simp only [IntegralMixedChronologicalFrame.Descriptor.pointProducer,dite_eq_right hi,
      IntegralMixedChronologicalFrame.Descriptor.freeCount]

theorem code_count (n birth : ℕ) (labels : List Bool) :
    WordListRecords.count (code n birth labels)=n+1 :=by
  simp only [code,WordListRecords.count_encode,List.length_map,List.length_range]

theorem code_lookup (n birth : ℕ) (labels : List Bool) (i : Fin (n+1)) :
    Nat.fromBitsLE (WordList.get (code n birth labels) i.val)=producer n birth labels i.val :=by
  simp only [code,WordList.get_encode,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some,BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem code_lookup_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (i : Fin (n+1)) :
    Nat.fromBitsLE (WordList.get (code n birth (IntegralMixedChronologicalFrameCode.labels d)) i.val)=
      (d.pointProducer i).val :=(code_lookup n birth _ i).trans (producer_actual d i)

end LeanCanny.Encoding.IntegralMixedChronologicalPointSignatureCode

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameDecode
public import LeanCanny.Geometry.IntegralMixedChronologicalFrameFreeze
/-! # Native endpoint labels extend a frozen descriptor at the same birth

Raw label words are read by their original natural value and encoded
canonically. Appending one existing producer consumes no scalar birth.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def entry (w : List Bool) (a i : ℕ):=BinaryNatCode.encode
  (if i<WordListRecords.count w then Nat.fromBitsLE (WordList.get w i) else a)
def appendLabels (w : List Bool) (a : ℕ):=
  WordList.encode ((List.range (WordListRecords.count w+1)).map (entry w a))

theorem append_count (w : List Bool) (a : ℕ) :
    WordListRecords.count (appendLabels w a)=WordListRecords.count w+1 :=by
  simp only [appendLabels,WordListRecords.count_encode,List.length_map,List.length_range]

theorem append_lookup_old (w : List Bool) (a i : ℕ) (hi : i<WordListRecords.count w) :
    Nat.fromBitsLE (WordList.get (appendLabels w a) i)=Nat.fromBitsLE (WordList.get w i) :=by
  rw [appendLabels,WordList.get_encode,List.getElem?_eq_getElem (by
    simp only [List.length_map,List.length_range];omega)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,entry,ite_eq_left hi,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem append_lookup_last (w : List Bool) (a : ℕ) :
    Nat.fromBitsLE (WordList.get (appendLabels w a) (WordListRecords.count w))=a :=by
  rw [appendLabels,WordList.get_encode,List.getElem?_eq_getElem (by
    simp only [List.length_map,List.length_range];omega)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,entry,Nat.lt_irrefl,ite_false,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem appendLabels_FP {w : List Bool→List Bool} {a : List Bool→ℕ}
    (hw : w∈FP) (ha : BinaryFn a) : (fun q=>appendLabels (w q) (a q))∈FP :=by
  have HK:=WordListRecords.count_unary.comp (mem_FP_comp pairFst_mem_FP hw)
  have HL : (fun p=>WordList.get (w (pairFst p)) (pairSnd p).length)∈FP:=by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hw)
      (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP)
    intro p
    simp only [WordList.reader,Function.comp_apply,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  have HV:=BinaryFn.ite ((BinaryFn.ofUnary UnaryFn.index).lt (BinaryFn.ofUnary HK))
    (BinaryFn.fromBits HL) (ha.comp pairFst_mem_FP)
  have HE:=mem_FP_pair HV.bits_mem_FP (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE
    (((WordListRecords.count_unary.comp hw).add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [appendLabels,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,entry]

def Good (n birth : ℕ) (w : List Bool) (a : ℕ) : Prop:=
  IntegralMixedChronologicalFrameCode.Good n birth w ∧ WordListRecords.count w<n+1 ∧ a<birth

theorem append_good_iff (n birth : ℕ) (w : List Bool) (a : ℕ) :
    IntegralMixedChronologicalFrameCode.Good n birth (appendLabels w a) ↔Good n birth w a :=by
  constructor
  · intro H
    have HC : WordListRecords.count w+1≤n+1:=by simpa only [append_count] using H.1
    refine ⟨⟨by omega,?_⟩,by omega,?_⟩
    · intro i hi
      have HI:=H.2 i (by rw [append_count];omega)
      rwa [append_lookup_old w a i hi] at HI
    · have HI:=H.2 (WordListRecords.count w) (by rw [append_count];omega)
      rwa [append_lookup_last] at HI
  · rintro ⟨H,hk,ha⟩
    refine ⟨by rw [append_count];omega,?_⟩
    intro i hi
    rw [append_count] at hi
    by_cases h : i<WordListRecords.count w
    · rw [append_lookup_old w a i h]
      exact H.2 i h
    · have HE : i=WordListRecords.count w:=by omega
      rw [HE,append_lookup_last]
      exact ha

theorem good_FP {n birth a : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (ha : BinaryFn a) (hw : w∈FP) :
    FPPred (fun q=>Good (n q) (birth q) (w q) (a q)) :=
  (IntegralMixedChronologicalFrameCode.good_FP hn hb hw).and
    (((BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)).lt
      ((BinaryFn.ofUnary hn).add (BinaryFn.const 1))).and (ha.lt hb))

def code (n : ℕ) (w : List Bool) (a g j : ℕ):=
  IntegralMixedChronologicalFrameCode.code n (appendLabels w a) g j

theorem code_FP {n a g j : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (ha : BinaryFn a) (hg : BinaryFn g) (hj : BinaryFn j) (hw : w∈FP) :
    (fun q=>code (n q) (w q) (a q) (g q) (j q))∈FP :=
  IntegralMixedChronologicalFrameCode.code_FP hn hg hj (appendLabels_FP hw ha)

def PointGood (n birth : ℕ) (w : List Bool) (a g j : ℕ) : Prop:=
  Good n birth w a ∧ WordListRecords.count w+1≤g ∧ g<n+1 ∧ WordListRecords.count w+1≤j ∧ j<n+1

theorem point_good_iff (n birth : ℕ) (w : List Bool) (a g j : ℕ) :
    IntegralMixedChronologicalFrameCode.PointGood n birth (appendLabels w a) g j ↔PointGood n birth w a g j :=by
  unfold IntegralMixedChronologicalFrameCode.PointGood PointGood
  rw [append_good_iff,append_count]

theorem pointGood_FP {n birth a g j : List Bool→ℕ} {w : List Bool→List Bool}
    (hn : UnaryFn n) (hb : BinaryFn birth) (ha : BinaryFn a) (hg : BinaryFn g) (hj : BinaryFn j) (hw : w∈FP) :
    FPPred (fun q=>PointGood (n q) (birth q) (w q) (a q) (g q) (j q)) :=by
  have HK:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)).add (BinaryFn.const 1)
  have HN:=(BinaryFn.ofUnary hn).add (BinaryFn.const 1)
  exact (good_FP hn hb ha hw).and ((HK.le hg).and ((hg.lt HN).and ((HK.le hj).and (hj.lt HN))))

end LeanCanny.Encoding.IntegralMixedChronologicalEndpointCode

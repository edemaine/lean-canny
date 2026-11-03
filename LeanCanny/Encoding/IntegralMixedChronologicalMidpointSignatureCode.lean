/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointReadback
public import LeanCanny.Encoding.IntegralMixedChronologicalFrameCodeActual
/-! # Native midpoint signatures with an explicit mean feature

The mean holds TWO original producer labels. Every other field contains
one actual frozen or captured producer. No scalar alias is invented.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureCode
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedChronologicalMidpointSignature
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def producerWord (a : ℕ):=pair [] (BinaryNatCode.encode a)
def meanWord (a b : ℕ):=pair [true] (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b))

def featureWord {cap : ℕ} : Feature cap→List Bool
  | .producer a=>producerWord a.val
  | .mean a b=>meanWord a.val b.val

def entry (n birth : ℕ) (labels : List Bool) (a b i : ℕ):=
  if i<WordListRecords.count labels then producerWord (Nat.fromBitsLE (WordList.get labels i))
  else if i=WordListRecords.count labels then meanWord a b
  else producerWord (birth+(n+1-(WordListRecords.count labels+1))-1-(i-(WordListRecords.count labels+1)))

def code (n birth : ℕ) (labels : List Bool) (a b : ℕ):=
  WordList.encode ((List.range (n+1)).map (entry n birth labels a b))

theorem code_FP {n birth a b : List Bool→ℕ} {labels : List Bool→List Bool}
    (hn : UnaryFn n) (hm : BinaryFn birth) (ha : BinaryFn a) (hb : BinaryFn b) (hw : labels∈FP) :
    (fun q=>code (n q) (birth q) (labels q) (a q) (b q))∈FP :=by
  have HW:=mem_FP_comp pairFst_mem_FP hw
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp HW)
  have HI:=BinaryFn.ofUnary UnaryFn.index
  have HL:=BinaryFn.fromBits (mem_FP_comp (mem_FP_pair HW HI.bits_mem_FP) WordList.reader_FP)
  have HN : BinaryFn (fun p=>n (pairFst p)):=(BinaryFn.ofUnary hn).comp pairFst_mem_FP
  have HM : BinaryFn (fun p=>birth (pairFst p)):=hm.comp pairFst_mem_FP
  have HA : BinaryFn (fun p=>a (pairFst p)):=ha.comp pairFst_mem_FP
  have HB : BinaryFn (fun p=>b (pairFst p)):=hb.comp pairFst_mem_FP
  have HQ:=(HN.add (BinaryFn.const 1)).sub (HK.add (BinaryFn.const 1))
  have HP:=((HM.add HQ).sub (BinaryFn.const 1)).sub (HI.sub (HK.add (BinaryFn.const 1)))
  have HF:=mem_FP_pair (constFn_mem_FP []) HP.bits_mem_FP
  have HO:=mem_FP_pair (constFn_mem_FP []) HL.bits_mem_FP
  have HE:=mem_FP_pair (constFn_mem_FP [true]) (mem_FP_pair
    HA.bits_mem_FP HB.bits_mem_FP)
  have HC:=(HI.lt HK).ite_mem_FP HO ((HI.eq HK).ite_mem_FP HE HF)
  apply mem_FP_of_eq (flatMap_range_mem_FP (mem_FP_pair HC (constFn_mem_FP []))
    ((hn.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [code,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,entry,producerWord,meanWord,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,WordList.reader,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

theorem entry_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (a b : Fin birth) (i : Fin (n+1)) :
    entry n birth (IntegralMixedChronologicalFrameCode.labels d) a.val b.val i.val=
      featureWord (signature d a b i) :=by
  unfold entry
  rw [IntegralMixedChronologicalFrameCode.labels_count]
  by_cases hi : i.val<d.labels.length
  · rw [ite_eq_left hi,IntegralMixedChronologicalFrameCode.labels_lookup d i.val hi]
    simp only [signature,dite_eq_left hi,featureWord,retainLabel]
  · rw [ite_eq_right hi]
    by_cases hm : i.val=d.labels.length
    · rw [ite_eq_left hm,signature_mean d a b i hm]
      rfl
    · rw [ite_eq_right hm]
      simp only [signature,dite_eq_right hi,dite_eq_right hm,featureWord,freeCount]

theorem code_count (n birth : ℕ) (labels : List Bool) (a b : ℕ) :
    WordListRecords.count (code n birth labels a b)=n+1 :=by
  simp only [code,WordListRecords.count_encode,List.length_map,List.length_range]

theorem code_lookup (n birth : ℕ) (labels : List Bool) (a b : ℕ) (i : Fin (n+1)) :
    WordList.get (code n birth labels a b) i.val=entry n birth labels a b i.val :=by
  simp only [code,WordList.get_encode,List.getElem?_map,List.getElem?_range i.isLt,Option.map_some,Option.getD_some]

theorem code_lookup_actual {n birth : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (a b : Fin birth) (i : Fin (n+1)) :
    WordList.get (code n birth (IntegralMixedChronologicalFrameCode.labels d) a.val b.val) i.val=
      featureWord (signature d a b i) :=(code_lookup n birth _ _ _ i).trans (entry_actual d a b i)

end LeanCanny.Encoding.IntegralMixedChronologicalMidpointSignatureCode

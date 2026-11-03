/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalPointSignatureCode
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
/-! # Native scalar comparisons identify all captured physical coordinates

The two original contexts and full words are retained. A pair table compares
the coordinate producers of their independently constructed signatures.
The cost is the existing original-only field-list decider. The geometric
conclusion requires the actual coordinate readbacks; equal scalar fields
alone do not infer source, frame or command provenance.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def pairs (dimension : ℕ) (left right : List Bool) :=WordList.encode
  ((List.range (dimension+1)).map (fun i=>pair (WordList.get left i) (WordList.get right i)))

theorem pairs_FP {dimension : List Bool→ℕ} {left right : List Bool→List Bool}
    (hd : UnaryFn dimension) (hl : left∈FP) (hr : right∈FP) :
    (fun q=>pairs (dimension q) (left q) (right q))∈FP :=by
  have HE (f : List Bool→List Bool) (hf : f∈FP) :
      (fun p=>WordList.get (f (pairFst p)) (pairSnd p).length)∈FP:=by
    apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hf)
      (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP)
    intro p
    simp only [WordList.reader,Function.comp_apply,pairFst_pair,pairSnd_pair,
      BinaryNatCode.encode,Nat.fromBitsLE_bits]
  apply mem_FP_of_eq (flatMap_range_mem_FP
    (mem_FP_pair (mem_FP_pair (HE left hl) (HE right hr)) (constFn_mem_FP []))
    ((hd.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [pairs,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    pairFst_pair,pairSnd_pair,List.length_replicate]

theorem pairs_count (dimension : ℕ) (left right : List Bool) :
    WordListRecords.count (pairs dimension left right)=dimension+1 :=by
  simp only [pairs,WordListRecords.count_encode,List.length_map,List.length_range]

theorem pairs_lookup (dimension : ℕ) (left right : List Bool) (i : Fin (dimension+1)) :
    WordList.get (pairs dimension left right) i.val=pair (WordList.get left i.val) (WordList.get right i.val) :=by
  simp only [pairs,WordList.get_encode,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some]

def signaturePairs {dimension a b : ℕ} (d : IntegralMixedChronologicalFrame.Descriptor dimension a)
    (e : IntegralMixedChronologicalFrame.Descriptor dimension b) :=pairs dimension
  (IntegralMixedChronologicalPointSignatureCode.code dimension a (IntegralMixedChronologicalFrameCode.labels d))
  (IntegralMixedChronologicalPointSignatureCode.code dimension b (IntegralMixedChronologicalFrameCode.labels e))

theorem signaturePairs_lookup {dimension a b : ℕ}
    (d : IntegralMixedChronologicalFrame.Descriptor dimension a)
    (e : IntegralMixedChronologicalFrame.Descriptor dimension b) (i : Fin (dimension+1)) :
    IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (signaturePairs d e) i.val)=(d.pointProducer i).val ∧
    IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (signaturePairs d e) i.val)=(e.pointProducer i).val :=by
  unfold signaturePairs
  rw [pairs_lookup]
  simp only [IntegralMixedPhysicalFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,IntegralMixedChronologicalPointSignatureCode.code_lookup_actual,and_self]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

theorem language_points_iff {dimension a b : ℕ}
    (d : IntegralMixedChronologicalFrame.Descriptor dimension a)
    (e : IntegralMixedChronologicalFrame.Descriptor dimension b)
    (cL wL cR wR : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR)
    (hca : a+d.freeCount≤IntegralMixedPhysicalFieldEquality.count hn ht ha hR cL)
    (hcb : b+e.freeCount≤IntegralMixedPhysicalFieldEquality.count hn ht ha hR cR)
    (p q : Fin (dimension+1)→ℝ)
    (HL : ∀i,IntegralMixedPhysicalFieldEquality.point hn ht ha hR cL wL hL (d.pointProducer i).val=p i)
    (HR : ∀i,IntegralMixedPhysicalFieldEquality.point hn ht ha hR cR wR hR' (e.pointProducer i).val=q i) :
    IntegralMixedPhysicalFieldEqualityList.packet cL wL cR wR (signaturePairs d e)∈
      IntegralMixedPhysicalFieldEqualityList.language hn ht ha hR ↔p=q :=by
  have HC : WordListRecords.count (signaturePairs d e)=dimension+1:=pairs_count _ _ _
  have HB : ∀i<WordListRecords.count (signaturePairs d e),
      IntegralMixedPhysicalFieldEqualityList.label false (WordList.get (signaturePairs d e) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha hR cL ∧
      IntegralMixedPhysicalFieldEqualityList.label true (WordList.get (signaturePairs d e) i)<
        IntegralMixedPhysicalFieldEquality.count hn ht ha hR cR:=by
    intro i hi
    have HI : i<dimension+1:=by simpa only [HC] using hi
    obtain ⟨HL,HR⟩:=signaturePairs_lookup d e ⟨i,HI⟩
    rw [HL,HR]
    exact ⟨(d.pointProducer ⟨i,HI⟩).isLt.trans_le hca,(e.pointProducer ⟨i,HI⟩).isLt.trans_le hcb⟩
  rw [IntegralMixedPhysicalFieldEqualityList.language_packet_iff hn ht ha hR cL wL cR wR _ hL hR' HB]
  constructor
  · intro H
    funext i
    have HE:=H i.val (by rw [HC];exact i.isLt)
    obtain ⟨HA,HB⟩:=signaturePairs_lookup d e i
    rw [HA,HB,HL,HR] at HE
    exact HE
  · intro HE i hi
    have HI : i<dimension+1:=by simpa only [HC] using hi
    obtain ⟨HA,HB⟩:=signaturePairs_lookup d e ⟨i,HI⟩
    rw [HA,HB,HL,HR,HE]

end LeanCanny.Encoding.IntegralMixedPhysicalPointSignatureComparison

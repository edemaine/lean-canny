/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
/-! # Original syntax for one optional slab endpoint

The six fields are kind, chronological producer, coordinate, ordinary cut
tag, factor choice and stored degree. Kind zero retains an OLD producer;
kind one appends the first-free critical point; kind two appends a cut.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def spec (kind producer coordinate tag choice degree : ℕ) :=
  WordList.encode ([kind,producer,coordinate,tag,choice,degree].map BinaryNatCode.encode)
def field (s : List Bool) (i : ℕ) :=Nat.fromBitsLE (WordList.get s i)
def canonical (s : List Bool) :=spec (field s 0) (field s 1) (field s 2) (field s 3) (field s 4) (field s 5)
def fresh (s : List Bool) :=if field s 0=0 then 0 else 1

theorem field_binary {s : List Bool→List Bool} (hs : s∈FP) (i : ℕ) : BinaryFn (fun q=>field (s q) i) :=by
  have H:=mem_FP_comp (mem_FP_pair hs (constFn_mem_FP (BinaryNatCode.encode i))) WordList.reader_FP
  exact (BinaryFn.fromBits H).of_eq (fun q=>by
    simp only [Function.comp_apply,WordList.reader_packet,field])

theorem spec_FP {kind producer coordinate tag choice degree : List Bool→ℕ}
    (hk : BinaryFn kind) (hp : BinaryFn producer) (hj : BinaryFn coordinate) (ht : BinaryFn tag)
    (hc : BinaryFn choice) (hd : BinaryFn degree) :
    (fun q=>spec (kind q) (producer q) (coordinate q) (tag q) (choice q) (degree q))∈FP :=
  mem_FP_pair hk.bits_mem_FP (mem_FP_pair hp.bits_mem_FP (mem_FP_pair hj.bits_mem_FP
    (mem_FP_pair ht.bits_mem_FP (mem_FP_pair hc.bits_mem_FP (mem_FP_pair hd.bits_mem_FP (constFn_mem_FP []))))))

theorem canonical_FP {s : List Bool→List Bool} (hs : s∈FP) : (fun q=>canonical (s q))∈FP :=
  spec_FP (field_binary hs 0) (field_binary hs 1) (field_binary hs 2)
    (field_binary hs 3) (field_binary hs 4) (field_binary hs 5)

theorem fresh_unary {s : List Bool→List Bool} (hs : s∈FP) : UnaryFn (fun q=>fresh (s q)) :=
  UnaryFn.ite ((field_binary hs 0).eq (BinaryFn.const 0)) (UnaryFn.const 0) (UnaryFn.const 1)

def code (n : ℕ) (labels s : List Bool) :=
  if field s 0=1 then
    IntegralMixedChronologicalFrameCode.code n labels (WordListRecords.count labels) (WordListRecords.count labels)
  else IntegralMixedChronologicalCutCode.code n labels (WordListRecords.count labels+1)
    (field s 2) (field s 3) (field s 4) (field s 5)
def codes (n : ℕ) (labels s : List Bool) :=if field s 0=0 then [] else [code n labels s]
def word (n : ℕ) (labels s : List Bool) :=WordList.encode (codes n labels s)

theorem code_FP {n : List Bool→ℕ} {labels s : List Bool→List Bool}
    (hn : UnaryFn n) (hw : labels∈FP) (hs : s∈FP) : (fun q=>code (n q) (labels q) (s q))∈FP :=by
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)
  exact ((field_binary hs 0).eq (BinaryFn.const 1)).ite_mem_FP
    (IntegralMixedChronologicalFrameCode.code_FP hn HK HK hw)
    (IntegralMixedChronologicalCutCode.code_FP hn (HK.add (BinaryFn.const 1))
      (field_binary hs 2) (field_binary hs 3) (field_binary hs 4) (field_binary hs 5) hw)

theorem word_FP {n : List Bool→ℕ} {labels s : List Bool→List Bool}
    (hn : UnaryFn n) (hw : labels∈FP) (hs : s∈FP) : (fun q=>word (n q) (labels q) (s q))∈FP :=by
  apply mem_FP_of_eq (((field_binary hs 0).eq (BinaryFn.const 0)).ite_mem_FP (constFn_mem_FP [])
    (mem_FP_pair (code_FP hn hw hs) (constFn_mem_FP [])))
  intro q
  simp only [word,codes]
  split_ifs <;> rfl

def Good (n B sourceCap oldBirth current : ℕ) (labels s : List Bool) : Prop :=
  s=canonical s ∧
  ((field s 0=0 ∧ field s 1<oldBirth ∧ field s 2=0 ∧ field s 3=0 ∧ field s 4=0 ∧ field s 5=0) ∨
   (field s 0=1 ∧ field s 1=current ∧ field s 2=WordListRecords.count labels ∧
    field s 3=0 ∧ field s 4=0 ∧ field s 5=0) ∨
   (field s 0=2 ∧ field s 1=current ∧
    IntegralMixedChronologicalCutCode.Bounds n current B sourceCap labels
      (WordListRecords.count labels+1) (field s 2) (field s 3) (field s 4) (field s 5)))

theorem good_FP {n B sourceCap oldBirth current : List Bool→ℕ} {labels s : List Bool→List Bool}
    (hn : UnaryFn n) (hB : UnaryFn B) (hc : BinaryFn sourceCap) (ho : BinaryFn oldBirth)
    (hm : BinaryFn current) (hw : labels∈FP) (hs : s∈FP) :
    FPPred (fun q=>Good (n q) (B q) (sourceCap q) (oldBirth q) (current q) (labels q) (s q)) :=by
  have H0:=field_binary hs 0
  have H1:=field_binary hs 1
  have H2:=field_binary hs 2
  have H3:=field_binary hs 3
  have H4:=field_binary hs 4
  have H5:=field_binary hs 5
  have HK:=BinaryFn.ofUnary (WordListRecords.count_unary.comp hw)
  exact (Brackets.stringEq_fppred hs (canonical_FP hs)).and
    (((H0.eq (BinaryFn.const 0)).and ((H1.lt ho).and ((H2.eq (BinaryFn.const 0)).and
      ((H3.eq (BinaryFn.const 0)).and ((H4.eq (BinaryFn.const 0)).and (H5.eq (BinaryFn.const 0))))))).or
    (((H0.eq (BinaryFn.const 1)).and ((H1.eq hm).and ((H2.eq HK).and
      ((H3.eq (BinaryFn.const 0)).and ((H4.eq (BinaryFn.const 0)).and (H5.eq (BinaryFn.const 0))))))).or
    ((H0.eq (BinaryFn.const 2)).and ((H1.eq hm).and
      (IntegralMixedChronologicalCutCode.bounds_FP hn hm hB hc (HK.add (BinaryFn.const 1)) H2 H3 H4 H5 hw)))))

theorem codes_length (n : ℕ) (labels s : List Bool) : (codes n labels s).length=fresh s :=by
  unfold codes fresh
  split_ifs <;> rfl

theorem producer_lt {n B sourceCap oldBirth current : ℕ} {labels s : List Bool}
    (h : Good n B sourceCap oldBirth current labels s) (hc : oldBirth≤current) :
    field s 1<current+fresh s :=by
  rcases h.2 with h|h|h
  · simp only [fresh,h.1,ite_true]
    omega
  · simp only [fresh,h.1,show (1:ℕ)≠0 by decide,ite_false,h.2.1]
    omega
  · simp only [fresh,h.1,show (2:ℕ)≠0 by decide,ite_false,h.2.1]
    omega

theorem checked_code {n B sourceCap oldBirth current : ℕ} {labels s : List Bool}
    (h : Good n B sourceCap oldBirth current labels s)
    (hf : IntegralMixedChronologicalFrameCode.Good n oldBirth labels) (hc : oldBirth≤current)
    (hk : WordListRecords.count labels<n+1) :
    (field s 0=0 ∧ field s 1<oldBirth ∧ codes n labels s=[]) ∨
    (field s 0=1 ∧ field s 1=current ∧
      IntegralMixedChronologicalFrameCode.PointGood n current labels (WordListRecords.count labels) (WordListRecords.count labels) ∧
      code n labels s=IntegralMixedChronologicalFrameCode.code n labels (WordListRecords.count labels) (WordListRecords.count labels)) ∨
    (field s 0=2 ∧ field s 1=current ∧
      IntegralMixedChronologicalCutCode.Bounds n current B sourceCap labels
        (WordListRecords.count labels+1) (field s 2) (field s 3) (field s 4) (field s 5) ∧
      code n labels s=IntegralMixedChronologicalCutCode.code n labels (WordListRecords.count labels+1)
        (field s 2) (field s 3) (field s 4) (field s 5)) :=by
  rcases h.2 with h|h|h
  · exact Or.inl ⟨h.1,h.2.1,by simp only [codes,h.1,ite_true]⟩
  · refine Or.inr (Or.inl ⟨h.1,h.2.1,?_,?_⟩)
    · exact ⟨⟨hf.1,fun i hi=>(hf.2 i hi).trans_le hc⟩,le_rfl,hk,le_rfl,hk⟩
    · simp only [code,h.1,ite_true]
  · refine Or.inr (Or.inr ⟨h.1,h.2.1,h.2.2,?_⟩)
    simp only [code,h.1,show (2:ℕ)≠1 by decide,ite_false]

end LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelOriginalBudget
/-! # Direct original prefix sums and frozen labels for a whole record chain

The input is pair metadata (pair rawRecords reservedProbe). Metadata is a
word list of three-field entries [leftSpec,rightSpec,side]. Labels are read
from earlier chosen producers, without iterating a growing framed state.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def packet (metadata raw probe : List Bool) :=pair metadata (pair raw probe)
def metadata (q : List Bool) :=pairFst q
def raw (q : List Bool) :=pairFst (pairSnd q)
def probe (q : List Bool) :=pairSnd (pairSnd q)
def depth (q : List Bool) :=WordListRecords.count (metadata q)
def entry (q : List Bool) (i : ℕ) :=WordList.get (metadata q) i
def left (q : List Bool) (i : ℕ) :=WordList.get (entry q i) 0
def right (q : List Bool) (i : ℕ) :=WordList.get (entry q i) 1
def sideWord (q : List Bool) (i : ℕ) :=WordList.get (entry q i) 2
def side (q : List Bool) (i : ℕ) :=decide (sideWord q i=[true])
def chosen (q : List Bool) (i : ℕ) :=IntegralMixedRoadmapEndpointSyntax.field
  (if sideWord q i=[true] then right q i else left q i) 1
def frozen (q : List Bool) (i : ℕ) :=WordList.encode
  ((List.range i).map (fun j=>BinaryNatCode.encode (chosen q j)))
def freshCount (q : List Bool) (i : ℕ) :=
  IntegralMixedRoadmapEndpointSyntax.fresh (left q i)+IntegralMixedRoadmapEndpointSyntax.fresh (right q i)
def blockCount (n : ℕ) (q : List Bool) (i : ℕ) :=freshCount q i+2+2*(n-i)
def prefixCount (n : ℕ) (q : List Bool) (i : ℕ) :=∑ j∈Finset.range i,blockCount n q j
def rawStart (n : ℕ) (q : List Bool) (i : ℕ) :=n+2+prefixCount n q i
def birth (n initial : ℕ) (q : List Bool) (i : ℕ) :=initial+rawStart n q i

theorem metadata_FP : metadata∈FP:=pairFst_mem_FP
theorem raw_FP : raw∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem probe_FP : probe∈FP:=mem_FP_comp (f:=pairSnd) (g:=pairSnd) pairSnd_mem_FP pairSnd_mem_FP
theorem depth_unary : UnaryFn depth:=WordListRecords.count_unary.comp metadata_FP

theorem get_FP {w : List Bool→List Bool} {i : List Bool→ℕ} (hw : w∈FP) (hi : BinaryFn i) :
    (fun q=>WordList.get (w q) (i q))∈FP :=by
  apply mem_FP_of_eq (mem_FP_comp (mem_FP_pair hw hi.bits_mem_FP) WordList.reader_FP)
  intro q
  simp only [Function.comp_apply,WordList.reader_packet]

theorem entry_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>entry (q p) (i p))∈FP :=
  get_FP (mem_FP_comp hq metadata_FP) (BinaryFn.ofUnary hi)
theorem left_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>left (q p) (i p))∈FP:=get_FP (entry_FP hq hi) (BinaryFn.const 0)
theorem right_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>right (q p) (i p))∈FP:=get_FP (entry_FP hq hi) (BinaryFn.const 1)
theorem sideWord_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>sideWord (q p) (i p))∈FP:=get_FP (entry_FP hq hi) (BinaryFn.const 2)
theorem chosen_binary {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    BinaryFn (fun p=>chosen (q p) (i p)) :=
  IntegralMixedRoadmapEndpointSyntax.field_binary
    ((Brackets.stringEq_fppred (sideWord_FP hq hi) (constFn_mem_FP [true])).ite_mem_FP
      (right_FP hq hi) (left_FP hq hi)) 1

theorem frozen_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>frozen (q p) (i p))∈FP :=by
  have HC:=chosen_binary (mem_FP_comp pairFst_mem_FP hq) UnaryFn.index
  apply mem_FP_of_eq (flatMap_range_mem_FP (mem_FP_pair HC.bits_mem_FP (constFn_mem_FP [])) (hi.replicate_mem_FP true))
  intro p
  simp only [frozen,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate]

theorem freshCount_unary {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    UnaryFn (fun p=>freshCount (q p) (i p)) :=
  (IntegralMixedRoadmapEndpointSyntax.fresh_unary (left_FP hq hi)).add
    (IntegralMixedRoadmapEndpointSyntax.fresh_unary (right_FP hq hi))
theorem blockCount_unary {n i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hq : q∈FP) (hi : UnaryFn i) : UnaryFn (fun p=>blockCount (n p) (q p) (i p)) :=
  ((freshCount_unary hq hi).add (UnaryFn.const 2)).add ((UnaryFn.const 2).mul (hn.sub hi))
theorem prefixCount_unary {n i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hq : q∈FP) (hi : UnaryFn i) : UnaryFn (fun p=>prefixCount (n p) (q p) (i p)) :=by
  have HF:=blockCount_unary (hn.comp pairFst_mem_FP) (mem_FP_comp pairFst_mem_FP hq) UnaryFn.index
  exact (hi.sum HF).of_eq (fun p=>by
    simp only [prefixCount,Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate])
theorem rawStart_unary {n i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hq : q∈FP) (hi : UnaryFn i) : UnaryFn (fun p=>rawStart (n p) (q p) (i p)) :=
  (hn.add (UnaryFn.const 2)).add (prefixCount_unary hn hq hi)
theorem birth_binary {n initial i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hm : BinaryFn initial) (hq : q∈FP) (hi : UnaryFn i) :
    BinaryFn (fun p=>birth (n p) (initial p) (q p) (i p)) :=
  hm.add (BinaryFn.ofUnary (rawStart_unary hn hq hi))

theorem frozen_count (q : List Bool) (i : ℕ) :WordListRecords.count (frozen q i)=i :=by
  simp only [frozen,WordListRecords.count_encode,List.length_map,List.length_range]
theorem frozen_lookup (q : List Bool) (i j : ℕ) (hj : j < i) :
    Nat.fromBitsLE (WordList.get (frozen q i) j)=chosen q j :=by
  rw [frozen,WordList.get_encode,List.getElem?_eq_getElem (by
    simpa only [List.length_map,List.length_range] using hj)]
  simp only [Option.getD_some,List.getElem_map,List.getElem_range,BinaryNatCode.encode,Nat.fromBitsLE_bits]
theorem prefixCount_succ (n : ℕ) (q : List Bool) (i : ℕ) :
    prefixCount n q (i+1)=prefixCount n q i+blockCount n q i:=Finset.sum_range_succ _ _
theorem rawStart_succ (n : ℕ) (q : List Bool) (i : ℕ) :
    rawStart n q (i+1)=rawStart n q i+blockCount n q i :=by
  rw [rawStart,prefixCount_succ,rawStart]
  omega

theorem frozen_succ (q : List Bool) (i : ℕ) :
    frozen q (i+1)=IntegralMixedChronologicalEndpointCode.appendLabels (frozen q i) (chosen q i) :=by
  change WordList.encode ((List.range (i+1)).map (fun j=>BinaryNatCode.encode (chosen q j)))=_
  unfold IntegralMixedChronologicalEndpointCode.appendLabels
  rw [frozen_count]
  apply congrArg WordList.encode
  apply List.map_congr_left
  intro j hj
  simp only [IntegralMixedChronologicalEndpointCode.entry,frozen_count]
  split_ifs with hji
  · rw [frozen_lookup q i j hji]
  · have HJ : j=i:=by have H:=List.mem_range.mp hj;omega
    rw [HJ]

theorem freshCount_le (q : List Bool) (i : ℕ) :freshCount q i≤2 :=by
  unfold freshCount IntegralMixedRoadmapEndpointSyntax.fresh
  split_ifs <;> omega

theorem prefixCount_bound (n : ℕ) (q : List Bool) (i : ℕ) :i≤n+1 →
    prefixCount n q i+(n+1-i)*(n+4-i)≤(n+1)*(n+4) :=by
  induction i with
  | zero=>intro _;simp only [prefixCount,Finset.range_zero,Finset.sum_empty,Nat.sub_zero,Nat.zero_add];exact le_rfl
  | succ i ih=>
    intro hi
    have IH:=ih (by omega)
    have HF:=freshCount_le q i
    rw [prefixCount_succ]
    unfold blockCount
    have H1 : n+1-i=n-i+1:=by omega
    have H2 : n+4-i=n-i+4:=by omega
    have H3 : n+1-(i+1)=n-i:=by omega
    have H4 : n+4-(i+1)=n-i+3:=by omega
    rw [H1,H2] at IH
    rw [H3,H4]
    nlinarith

theorem rawStart_bound (n : ℕ) (q : List Bool) (i : ℕ) (hi : i≤n+1) :
    rawStart n q i≤IntegralMixedRoadmapRecordChain.recordBound n :=by
  have H:=prefixCount_bound n q i hi
  unfold rawStart IntegralMixedRoadmapRecordChain.recordBound
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapChain

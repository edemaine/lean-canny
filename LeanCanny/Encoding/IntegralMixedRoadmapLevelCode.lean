/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapEndpointSyntax
public import LeanCanny.Encoding.IntegralMixedChronologicalEndpointRaw
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointRaw
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointCompanionCode
public import LeanCanny.Encoding.IntegralMixedChronologicalCompanionCode
/-! # Literal chronological compilation of one recursive roadmap level

Packet: pair oldLabels (pair leftSpec (pair rightSpec (pair side emittedSlice))).
The child freezes the chosen endpoint's producer, never a physical-point head.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapLevel
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (labels left right : List Bool) (side : Bool) (slice : List Bool) :=
  pair labels (pair left (pair right (pair (if side then [true] else []) slice)))
def labels (q : List Bool) :=pairFst q
def left (q : List Bool) :=pairFst (pairSnd q)
def right (q : List Bool) :=pairFst (pairSnd (pairSnd q))
def sideWord (q : List Bool) :=pairFst (pairSnd (pairSnd (pairSnd q)))
def slice (q : List Bool) :=pairSnd (pairSnd (pairSnd (pairSnd q)))
def side (q : List Bool) :=decide (sideWord q=[true])
def k (q : List Bool) :=WordListRecords.count (labels q)
def g (q : List Bool) :=k q+1
def freeCount (n : ℕ) (q : List Bool) :=n+1-g q
def producer (isRight : Bool) (q : List Bool) :=
  IntegralMixedRoadmapEndpointSyntax.field (if isRight then right q else left q) 1
def chosen (q : List Bool) :=if sideWord q=[true] then producer true q else producer false q
def childLabels (q : List Bool) :=IntegralMixedChronologicalEndpointCode.appendLabels (labels q) (chosen q)
def freshLeft (q : List Bool) :=IntegralMixedRoadmapEndpointSyntax.fresh (left q)
def freshRight (q : List Bool) :=IntegralMixedRoadmapEndpointSyntax.fresh (right q)
def afterEndpoints (birth : ℕ) (q : List Bool) :=birth+freshLeft q+freshRight q
def childBirth (n birth : ℕ) (q : List Bool) :=afterEndpoints birth q+1+freeCount n q
def endBirth (n birth : ℕ) (q : List Bool) :=afterEndpoints birth q+2+2*freeCount n q
def emittedCount (n : ℕ) (q : List Bool) :=freshLeft q+freshRight q+2+2*freeCount n q
def rawSlice (raw : List Bool) (start count : ℕ) :=
  WordList.encode ((List.range count).map (fun i=>WordList.get raw (start+i)))

theorem labels_FP : labels∈FP:=pairFst_mem_FP
theorem left_FP : left∈FP:=mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem right_FP : right∈FP:=mem_FP_comp (f:=pairSnd) (g:=left) pairSnd_mem_FP left_FP
theorem sideWord_FP : sideWord∈FP:=mem_FP_comp (f:=pairSnd) (g:=right) pairSnd_mem_FP right_FP
theorem slice_FP : slice∈FP:=by
  have H:=mem_FP_comp (f:=pairSnd) (g:=pairSnd) pairSnd_mem_FP pairSnd_mem_FP
  exact mem_FP_comp (f:=fun q=>pairSnd (pairSnd q)) (g:=fun q=>pairSnd (pairSnd q)) H H
theorem k_unary : UnaryFn k:=WordListRecords.count_unary.comp labels_FP
theorem g_unary : UnaryFn g:=k_unary.add (UnaryFn.const 1)
theorem freeCount_unary {n : List Bool→ℕ} (hn : UnaryFn n) : UnaryFn (fun q=>freeCount (n q) q):=
  (hn.add (UnaryFn.const 1)).sub g_unary
theorem producer_binary (isRight : Bool) : BinaryFn (producer isRight) :=by
  cases isRight
  · exact IntegralMixedRoadmapEndpointSyntax.field_binary left_FP 1
  · exact IntegralMixedRoadmapEndpointSyntax.field_binary right_FP 1
theorem chosen_binary : BinaryFn chosen:=BinaryFn.ite
  (Brackets.stringEq_fppred sideWord_FP (constFn_mem_FP [true])) (producer_binary true) (producer_binary false)
theorem childLabels_FP : childLabels∈FP:=IntegralMixedChronologicalEndpointCode.appendLabels_FP labels_FP chosen_binary
theorem freshLeft_unary : UnaryFn freshLeft:=IntegralMixedRoadmapEndpointSyntax.fresh_unary left_FP
theorem freshRight_unary : UnaryFn freshRight:=IntegralMixedRoadmapEndpointSyntax.fresh_unary right_FP
theorem afterEndpoints_binary {birth : List Bool→ℕ} (hb : BinaryFn birth) : BinaryFn (fun q=>afterEndpoints (birth q) q):=
  (hb.add (BinaryFn.ofUnary freshLeft_unary)).add (BinaryFn.ofUnary freshRight_unary)
theorem endBirth_binary {n birth : List Bool→ℕ} (hn : UnaryFn n) (hb : BinaryFn birth) :
    BinaryFn (fun q=>endBirth (n q) (birth q) q) :=
  ((afterEndpoints_binary hb).add (BinaryFn.const 2)).add
    ((BinaryFn.const 2).mul (BinaryFn.ofUnary (freeCount_unary hn)))
theorem emittedCount_unary {n : List Bool→ℕ} (hn : UnaryFn n) : UnaryFn (fun q=>emittedCount (n q) q) :=
  (((freshLeft_unary.add freshRight_unary).add (UnaryFn.const 2))).add
    ((UnaryFn.const 2).mul (freeCount_unary hn))

theorem rawSlice_FP {raw : List Bool→List Bool} {start count : List Bool→ℕ}
    (hr : raw∈FP) (hs : BinaryFn start) (hc : UnaryFn count) :
    (fun q=>rawSlice (raw q) (start q) (count q))∈FP :=by
  have HS : BinaryFn (fun p=>start (pairFst p)):=hs.comp pairFst_mem_FP
  have HI:=HS.add (BinaryFn.ofUnary UnaryFn.index)
  have HG:=mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hr) HI.bits_mem_FP) WordList.reader_FP
  apply mem_FP_of_eq (flatMap_range_mem_FP (mem_FP_pair HG (constFn_mem_FP [])) (hc.replicate_mem_FP true))
  intro q
  simp only [rawSlice,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,Function.comp_apply,
    pairFst_pair,pairSnd_pair,List.length_replicate,WordList.reader,BinaryNatCode.encode,Nat.fromBitsLE_bits]

def midpointAnchor (n : ℕ) (q : List Bool) :=IntegralMixedChronologicalMidpointCode.code n (labels q)
  (producer false q) (producer true q) (g q) (g q)
def childAnchor (n : ℕ) (q : List Bool) :=IntegralMixedChronologicalEndpointCode.code n (labels q)
  (chosen q) (g q) (g q)
def codes (n : ℕ) (q : List Bool) :=
  IntegralMixedRoadmapEndpointSyntax.codes n (labels q) (left q) ++
  IntegralMixedRoadmapEndpointSyntax.codes n (labels q) (right q) ++ [midpointAnchor n q] ++
  IntegralMixedChronologicalMidpointCompanionCode.codes n (labels q) (producer false q) (producer true q) (g q) ++
  [childAnchor n q] ++IntegralMixedChronologicalCompanionCode.codes n (childLabels q) (g q)
def compiled (n : ℕ) (q : List Bool) :=WordList.encode (codes n q)

theorem compiled_packet (n : ℕ) (w l r : List Bool) (s : Bool) (x y : List Bool) :
    compiled n (packet w l r s x)=compiled n (packet w l r s y) :=by
  simp only [compiled,codes,midpointAnchor,childAnchor,childLabels,chosen,producer,g,k,
    labels,left,right,sideWord,packet,pairFst_pair,pairSnd_pair]

theorem encode_append (xs ys : List (List Bool)) : WordList.encode (xs++ys)=WordList.encode xs++WordList.encode ys :=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.cons_append,WordList.encode,ih,pair,List.append_assoc]

theorem compiled_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun q=>compiled (n q) q)∈FP :=by
  have HM:=IntegralMixedChronologicalMidpointCode.code_FP hn (producer_binary false) (producer_binary true)
    (BinaryFn.ofUnary g_unary) (BinaryFn.ofUnary g_unary) labels_FP
  have HE:=IntegralMixedChronologicalEndpointCode.code_FP hn chosen_binary
    (BinaryFn.ofUnary g_unary) (BinaryFn.ofUnary g_unary) labels_FP
  have HMC:=IntegralMixedChronologicalMidpointCompanionCode.word_FP hn (producer_binary false) (producer_binary true)
    (BinaryFn.ofUnary g_unary) labels_FP
  have HEC:=IntegralMixedChronologicalCompanionCode.word_FP hn (BinaryFn.ofUnary g_unary) childLabels_FP
  apply mem_FP_of_eq (appendFn_mem_FP
    (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
      (IntegralMixedRoadmapEndpointSyntax.word_FP hn labels_FP left_FP)
      (IntegralMixedRoadmapEndpointSyntax.word_FP hn labels_FP right_FP))
      (mem_FP_pair HM (constFn_mem_FP []))) HMC) (mem_FP_pair HE (constFn_mem_FP []))) HEC)
  intro q
  simp only [compiled,codes,encode_append,WordList.encode,
    IntegralMixedRoadmapEndpointSyntax.word,IntegralMixedChronologicalMidpointCompanionCode.word,
    IntegralMixedChronologicalCompanionCode.word,midpointAnchor,childAnchor,List.append_assoc]

theorem child_labels_count (q : List Bool) : WordListRecords.count (childLabels q)=k q+1 :=
  IntegralMixedChronologicalEndpointCode.append_count _ _

theorem codes_length (n : ℕ) (q : List Bool) :
    (codes n q).length=freshLeft q+freshRight q+2+2*freeCount n q :=by
  simp only [codes,List.length_append,IntegralMixedRoadmapEndpointSyntax.codes_length,
    List.length_singleton,IntegralMixedChronologicalMidpointCompanionCode.codes_length,
    IntegralMixedChronologicalCompanionCode.codes,List.length_map,List.length_range,child_labels_count]
  unfold freshLeft freshRight freeCount g k
  omega

theorem endBirth_eq (n birth : ℕ) (q : List Bool) :birth+(codes n q).length=endBirth n birth q :=by
  rw [codes_length]
  unfold endBirth afterEndpoints
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapLevel

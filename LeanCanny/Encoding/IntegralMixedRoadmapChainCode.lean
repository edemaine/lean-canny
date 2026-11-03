/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapChainPrefix
/-! # Whole-chain native compilation without a growing-state iterator -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapChain
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def withSlice (q : List Bool) (i : ℕ) (payload : List Bool) :=IntegralMixedRoadmapLevel.packet
  (frozen q i) (left q i) (right q i) (side q i) payload
def template (q : List Bool) (i : ℕ) :=withSlice q i []
def levelPacket (n : ℕ) (q : List Bool) (i : ℕ) :=withSlice q i
  (IntegralMixedRoadmapLevel.rawSlice (raw q) (rawStart n q i) (blockCount n q i))
def canonicalEntry (q : List Bool) (i : ℕ) :=WordList.encode
  [left q i,right q i,if side q i then [true] else []]
def seedCode (n : ℕ) :=IntegralMixedChronologicalFrameCode.code n [] 0 0
def seedCodes (n : ℕ) :=[seedCode n]++IntegralMixedChronologicalCompanionCode.codes n [] 0
def meaningfulCodes (n : ℕ) (q : List Bool) :=seedCodes n++
  (List.range (depth q)).flatMap (fun i=>IntegralMixedRoadmapLevel.codes n (template q i))
def paddingCount (n : ℕ) (q : List Bool) :=IntegralMixedRoadmapRecordChain.recordBound n-rawStart n q (depth q)
def compiledCodes (n : ℕ) (q : List Bool) :=meaningfulCodes n q++
  List.replicate (paddingCount n q) (seedCode n)++[probe q]
def compiled (n : ℕ) (q : List Bool) :=WordList.encode (compiledCodes n q)

theorem compiled_packet (n : ℕ) (m p x y : List Bool) :
    compiled n (packet m x p)=compiled n (packet m y p) :=by
  simp only [compiled,compiledCodes,meaningfulCodes,paddingCount,rawStart,prefixCount,blockCount,freshCount,
    template,withSlice,frozen,chosen,left,right,entry,side,sideWord,depth,metadata,probe,packet,pairFst_pair,pairSnd_pair]

theorem rawSlice_all (xs : List (List Bool)) :
    IntegralMixedRoadmapLevel.rawSlice (WordList.encode xs) 0 xs.length=WordList.encode xs :=by
  unfold IntegralMixedRoadmapLevel.rawSlice
  apply congrArg WordList.encode
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range]
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,Nat.zero_add,WordList.get_encode,
      List.getElem?_eq_getElem hj,Option.getD_some]

theorem withSlice_FP {q : List Bool→List Bool} {i : List Bool→ℕ} {payload : List Bool→List Bool}
    (hq : q∈FP) (hi : UnaryFn i) (hp : payload∈FP) : (fun p=>withSlice (q p) (i p) (payload p))∈FP :=by
  have HS:=(Brackets.stringEq_fppred (sideWord_FP hq hi) (constFn_mem_FP [true])).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])
  simpa only [withSlice,IntegralMixedRoadmapLevel.packet,side,decide_eq_true_eq] using
    mem_FP_pair (frozen_FP hq hi) (mem_FP_pair (left_FP hq hi) (mem_FP_pair (right_FP hq hi) (mem_FP_pair HS hp)))
theorem template_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>template (q p) (i p))∈FP :=withSlice_FP hq hi (constFn_mem_FP [])
theorem levelPacket_FP {n i : List Bool→ℕ} {q : List Bool→List Bool}
    (hn : UnaryFn n) (hq : q∈FP) (hi : UnaryFn i) : (fun p=>levelPacket (n p) (q p) (i p))∈FP :=
  withSlice_FP hq hi (IntegralMixedRoadmapLevel.rawSlice_FP (mem_FP_comp (f:=q) (g:=raw) hq raw_FP)
    (BinaryFn.ofUnary (rawStart_unary hn hq hi)) (blockCount_unary hn hq hi))
theorem canonicalEntry_FP {q : List Bool→List Bool} {i : List Bool→ℕ} (hq : q∈FP) (hi : UnaryFn i) :
    (fun p=>canonicalEntry (q p) (i p))∈FP :=by
  have HS:=(Brackets.stringEq_fppred (sideWord_FP hq hi) (constFn_mem_FP [true])).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])
  simpa only [canonicalEntry,WordList.encode,side,decide_eq_true_eq] using mem_FP_pair (left_FP hq hi)
    (mem_FP_pair (right_FP hq hi) (mem_FP_pair HS (constFn_mem_FP [])))

theorem seedCode_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun p=>seedCode (n p))∈FP :=
  IntegralMixedChronologicalFrameCode.code_FP hn (BinaryFn.const 0) (BinaryFn.const 0) (constFn_mem_FP [])
theorem seedWord_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun p=>WordList.encode (seedCodes (n p)))∈FP :=
  mem_FP_pair (seedCode_FP hn) (IntegralMixedChronologicalCompanionCode.word_FP hn (BinaryFn.const 0) (constFn_mem_FP []))

theorem compileAt_FP {n : List Bool→ℕ} {q : List Bool→List Bool} (hn : UnaryFn n) (hq : q∈FP) :
    (fun p=>IntegralMixedRoadmapLevel.compiled (n p) (q p))∈FP :=by
  have HW:=mem_FP_comp hq IntegralMixedRoadmapLevel.labels_FP
  have HL:=mem_FP_comp hq IntegralMixedRoadmapLevel.left_FP
  have HR:=mem_FP_comp hq IntegralMixedRoadmapLevel.right_FP
  have HA : BinaryFn (fun p=>IntegralMixedRoadmapLevel.producer false (q p)):=
    (IntegralMixedRoadmapLevel.producer_binary false).comp hq
  have HB : BinaryFn (fun p=>IntegralMixedRoadmapLevel.producer true (q p)):=
    (IntegralMixedRoadmapLevel.producer_binary true).comp hq
  have HG:=BinaryFn.ofUnary (IntegralMixedRoadmapLevel.g_unary.comp hq)
  have HC : BinaryFn (fun p=>IntegralMixedRoadmapLevel.chosen (q p)):=IntegralMixedRoadmapLevel.chosen_binary.comp hq
  have Hchild:=mem_FP_comp hq IntegralMixedRoadmapLevel.childLabels_FP
  have HM:=IntegralMixedChronologicalMidpointCode.code_FP hn HA HB HG HG HW
  have HE:=IntegralMixedChronologicalEndpointCode.code_FP hn HC HG HG HW
  have HMC:=IntegralMixedChronologicalMidpointCompanionCode.word_FP hn HA HB HG HW
  have HEC:=IntegralMixedChronologicalCompanionCode.word_FP hn HG Hchild
  apply mem_FP_of_eq (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (IntegralMixedRoadmapEndpointSyntax.word_FP hn HW HL) (IntegralMixedRoadmapEndpointSyntax.word_FP hn HW HR))
    (mem_FP_pair HM (constFn_mem_FP []))) HMC) (mem_FP_pair HE (constFn_mem_FP []))) HEC)
  intro p
  simp only [IntegralMixedRoadmapLevel.compiled,IntegralMixedRoadmapLevel.codes,IntegralMixedRoadmapLevel.encode_append,
    WordList.encode,IntegralMixedRoadmapEndpointSyntax.word,IntegralMixedChronologicalMidpointCompanionCode.word,
    IntegralMixedChronologicalCompanionCode.word,IntegralMixedRoadmapLevel.midpointAnchor,IntegralMixedRoadmapLevel.childAnchor,
    List.append_assoc,Function.comp_apply]

theorem encode_flatMap {α : Type} (xs : List α) (f : α→List (List Bool)) :
    WordList.encode (xs.flatMap f)=xs.flatMap (fun x=>WordList.encode (f x)) :=by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>simp only [List.flatMap_cons,IntegralMixedRoadmapLevel.encode_append,ih]

theorem levelWordAt_FP {n : List Bool→ℕ} {q : List Bool→List Bool} (hn : UnaryFn n) (hq : q∈FP) :
    (fun p=>WordList.encode ((List.range (depth (q p))).flatMap (fun i=>IntegralMixedRoadmapLevel.codes (n p) (template (q p) i))))∈FP :=by
  have HE:=compileAt_FP (hn.comp pairFst_mem_FP) (template_FP (mem_FP_comp pairFst_mem_FP hq) UnaryFn.index)
  apply mem_FP_of_eq (flatMap_range_mem_FP HE ((depth_unary.comp hq).replicate_mem_FP true))
  intro p
  simp only [Function.comp_apply,pairFst_pair,pairSnd_pair,List.length_replicate,
    IntegralMixedRoadmapLevel.compiled,encode_flatMap]
theorem paddingCountAt_unary {n : List Bool→ℕ} {q : List Bool→List Bool} (hn : UnaryFn n) (hq : q∈FP) :
    UnaryFn (fun p=>paddingCount (n p) (q p)) :=
  (IntegralMixedRoadmapRecordChain.recordBound_unary hn).sub (rawStart_unary hn hq (depth_unary.comp hq))
theorem compiledAt_FP {n : List Bool→ℕ} {q : List Bool→List Bool} (hn : UnaryFn n) (hq : q∈FP) :
    (fun p=>compiled (n p) (q p))∈FP :=by
  have HS:=seedCode_FP (hn.comp pairFst_mem_FP)
  have HP:=flatMap_range_mem_FP (mem_FP_pair HS (constFn_mem_FP [])) ((paddingCountAt_unary hn hq).replicate_mem_FP true)
  apply mem_FP_of_eq (appendFn_mem_FP (appendFn_mem_FP (appendFn_mem_FP
    (seedWord_FP hn) (levelWordAt_FP hn hq)) HP) (mem_FP_pair (mem_FP_comp (f:=q) (g:=probe) hq probe_FP) (constFn_mem_FP [])))
  intro p
  simp only [compiled,compiledCodes,meaningfulCodes,IntegralMixedRoadmapLevel.encode_append,
    WordList.encode,Function.comp_apply,pairFst_pair,List.length_replicate]
  have H : (List.range (paddingCount (n p) (q p))).flatMap (fun _=>pair (seedCode (n p)) [])=
      WordList.encode (List.replicate (paddingCount (n p) (q p)) (seedCode (n p))) :=by
    induction paddingCount (n p) (q p) with
    | zero=>rfl
    | succ d ih=>
      simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
        List.replicate_succ',IntegralMixedRoadmapLevel.encode_append,WordList.encode,ih]
  rw [H]

theorem compiled_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun p=>compiled (n p) p)∈FP :=
  compiledAt_FP hn id_mem_FP

theorem withSlice_k (q : List Bool) (i : ℕ) (payload : List Bool) :
    IntegralMixedRoadmapLevel.k (withSlice q i payload)=i :=by
  simp only [IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,withSlice,
    IntegralMixedRoadmapLevel.packet,pairFst_pair,frozen_count]
theorem withSlice_chosen (q : List Bool) (i : ℕ) (payload : List Bool) :
    IntegralMixedRoadmapLevel.chosen (withSlice q i payload)=chosen q i :=by
  by_cases h : sideWord q i=[true]
  all_goals simp only [IntegralMixedRoadmapLevel.chosen,IntegralMixedRoadmapLevel.sideWord,
    IntegralMixedRoadmapLevel.producer,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    withSlice,IntegralMixedRoadmapLevel.packet,pairFst_pair,pairSnd_pair,side,h,decide_true,decide_false,
    Bool.false_eq_true,ite_true,ite_false,chosen,show ([] : List Bool)≠[true] by decide]
theorem level_count (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.emittedCount n (levelPacket n q i)=blockCount n q i :=by
  simp only [IntegralMixedRoadmapLevel.emittedCount,IntegralMixedRoadmapLevel.freshLeft,
    IntegralMixedRoadmapLevel.freshRight,IntegralMixedRoadmapLevel.left,IntegralMixedRoadmapLevel.right,
    IntegralMixedRoadmapLevel.freeCount,IntegralMixedRoadmapLevel.g,levelPacket,withSlice,
    IntegralMixedRoadmapLevel.packet,IntegralMixedRoadmapLevel.k,IntegralMixedRoadmapLevel.labels,
    pairFst_pair,pairSnd_pair,frozen_count]
  simp only [Nat.add_sub_add_right]
  rfl
theorem level_compiled (n : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.compiled n (levelPacket n q i)=IntegralMixedRoadmapLevel.compiled n (template q i) :=
  IntegralMixedRoadmapLevel.compiled_packet _ _ _ _ _ _ _
theorem level_end (n initial : ℕ) (q : List Bool) (i : ℕ) :
    IntegralMixedRoadmapLevel.endBirth n (birth n initial q i) (levelPacket n q i)=birth n initial q (i+1) :=by
  have HE : ∀ m p, IntegralMixedRoadmapLevel.endBirth n m p=m+IntegralMixedRoadmapLevel.emittedCount n p:=by
    intro m p
    unfold IntegralMixedRoadmapLevel.endBirth IntegralMixedRoadmapLevel.afterEndpoints IntegralMixedRoadmapLevel.emittedCount
    omega
  rw [HE,level_count]
  unfold birth
  rw [rawStart_succ]
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapChain

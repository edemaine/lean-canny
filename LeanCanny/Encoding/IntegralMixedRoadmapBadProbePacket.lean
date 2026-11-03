/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalCutCode
public import LeanCanny.Encoding.IntegralMixedRoadmapLevelCode
public import LeanCanny.Encoding.IntegralMixedCausalRecordPlan
/-! # Native replacement of the reserved record by an ordinary bad probe

Base packet: candidate, raw table, full word, frozen labels, endpoint producers.
The outer hint has tag/physical-coordinate/choice/degree fields. The writer
preserves the candidate and every earlier raw record, and uses empty metadata.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def packet (candidate raw word labels left right : List Bool):=
  pair candidate (pair raw (pair word (pair labels (pair left right))))
def candidate (q : List Bool):=pairFst q
def raw (q : List Bool):=pairFst (pairSnd q)
def word (q : List Bool):=pairFst (pairSnd (pairSnd q))
def labels (q : List Bool):=pairFst (pairSnd (pairSnd (pairSnd q)))
def endpoints (q : List Bool):=pairSnd (pairSnd (pairSnd (pairSnd q)))
def producer (right : Bool) (q : List Bool):=
  Nat.fromBitsLE (if right then pairSnd (endpoints q) else pairFst (endpoints q))
def root (q : List Bool):=pair (candidate q) (pair (raw q) [])
def count (q : List Bool):=WordListRecords.count (raw q)
def prefixCodes (q : List Bool):=(List.range (count q-1)).map (WordList.get (raw q))
def prefixWord (q : List Bool):=WordList.encode (prefixCodes q)
def field (i : ℕ) (z : List Bool):=WordList.get (pairSnd z) i

theorem candidate_FP : candidate∈FP:=pairFst_mem_FP
theorem raw_FP : raw∈FP:=by polytime [raw]
theorem word_FP : word∈FP:=by polytime [word]
theorem labels_FP : labels∈FP:=by polytime [labels]
theorem producer_binary (right : Bool) : BinaryFn (producer right):=by
  cases right <;> exact BinaryFn.fromBits (by polytime [endpoints])
theorem root_FP : root∈FP:=mem_FP_pair candidate_FP (mem_FP_pair raw_FP (constFn_mem_FP []))
theorem count_unary : UnaryFn count:=WordListRecords.count_unary.comp raw_FP
theorem field_FP (i : ℕ) : field i∈FP:=by
  apply mem_FP_of_eq (mem_FP_comp (g:=WordList.reader)
    (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP (BinaryNatCode.encode i))) WordList.reader_FP)
  intro z
  simp only [Function.comp_apply,field,WordList.reader_packet]
theorem field_binary (i : ℕ) : BinaryFn (fun z=>Nat.fromBitsLE (field i z)):=BinaryFn.fromBits (field_FP i)

theorem prefixWord_FP : prefixWord∈FP:=by
  change (fun q=>WordList.encode (prefixCodes q))∈FP
  simpa only [IntegralMixedRoadmapLevel.rawSlice,prefixCodes,Nat.zero_add] using
    IntegralMixedRoadmapLevel.rawSlice_FP raw_FP (BinaryFn.const 0) (count_unary.sub (UnaryFn.const 1))

def probe (n : ℕ) (z : List Bool):=IntegralMixedChronologicalCutCode.code n
  (labels (pairFst z)) (WordListRecords.count (labels (pairFst z))+1)
  (Nat.fromBitsLE (field 1 z)) (Nat.fromBitsLE (field 0 z))
  (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))
def preparedRaw (n : ℕ) (z : List Bool):=WordList.encode (prefixCodes (pairFst z)++[probe n z])
def preparedRoot (n : ℕ) (z : List Bool):=
  pair (candidate (pairFst z)) (pair (preparedRaw n z) [])

theorem probe_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun z=>probe (n z) z)∈FP:=by
  have HL:=mem_FP_comp pairFst_mem_FP labels_FP
  have HG:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp HL)).add (BinaryFn.const 1)
  exact IntegralMixedChronologicalCutCode.code_FP hn HG (field_binary 1) (field_binary 0)
    (field_binary 2) (field_binary 3) HL

theorem preparedRaw_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun z=>preparedRaw (n z) z)∈FP:=by
  apply mem_FP_of_eq (appendFn_mem_FP (mem_FP_comp pairFst_mem_FP prefixWord_FP)
    (mem_FP_pair (probe_FP hn) (constFn_mem_FP [])))
  intro z
  simp only [preparedRaw,Function.comp_apply,prefixWord,IntegralMixedRoadmapLevel.encode_append,WordList.encode]

theorem preparedRoot_FP {n : List Bool→ℕ} (hn : UnaryFn n) : (fun z=>preparedRoot (n z) z)∈FP:=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP candidate_FP) (mem_FP_pair (preparedRaw_FP hn) (constFn_mem_FP []))

theorem prepared_candidate (n : ℕ) (z : List Bool) :
    pairFst (preparedRoot n z)=candidate (pairFst z):=pairFst_pair _ _

theorem prepared_count (n : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    IntegralMixedCausalRecordPlanBits.count (preparedRoot n z)=count (pairFst z) :=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,pairSnd_pair,pairFst_pair,preparedRaw,WordListRecords.count_encode,
    List.length_append,List.length_singleton,prefixCodes,List.length_map,List.length_range]
  omega

theorem prepared_lookup (n : ℕ) (z : List Bool) (i : ℕ) (hi : i<count (pairFst z)-1) :
    WordList.get (preparedRaw n z) i=WordList.get (raw (pairFst z)) i :=by
  have HL : i<(prefixCodes (pairFst z)).length:=by
    simp only [prefixCodes,List.length_map,List.length_range]
    exact hi
  rw [preparedRaw,WordList.get_encode,List.getElem?_append_left HL]
  simp only [prefixCodes,
    List.getElem?_map,List.getElem?_range hi,Option.map_some,Option.getD_some]

theorem prepared_last (n : ℕ) (z : List Bool) :
    WordList.get (preparedRaw n z) (count (pairFst z)-1)=probe n z :=by
  have HL : count (pairFst z)-1=(prefixCodes (pairFst z)).length:=by
    simp only [prefixCodes,List.length_map,List.length_range]
  rw [HL,preparedRaw,WordList.get_encode]
  simp

def creating (initial : ℕ) (q : List Bool):=initial+count q-1
def intervalContext (n initial : ℕ) (z : List Bool):=
  pair (preparedRoot n z) (pair (List.replicate (creating initial (pairFst z)) true)
    (pair (BinaryNatCode.encode (creating initial (pairFst z)-producer false (pairFst z)))
      (BinaryNatCode.encode (creating initial (pairFst z)-producer true (pairFst z)))))

theorem creating_unary {initial : List Bool→ℕ} {q : List Bool→List Bool}
    (hi : UnaryFn initial) (hq : q∈FP) : UnaryFn (fun z=>creating (initial z) (q z)):=
  (hi.add (count_unary.comp hq)).sub (UnaryFn.const 1)

theorem intervalContext_FP {n initial : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) :
    (fun z=>intervalContext (n z) (initial z) z)∈FP:=by
  have HM:=creating_unary hi pairFst_mem_FP
  have HL:=(BinaryFn.ofUnary HM).sub ((producer_binary false).comp pairFst_mem_FP)
  have HR:=(BinaryFn.ofUnary HM).sub ((producer_binary true).comp pairFst_mem_FP)
  exact mem_FP_pair (preparedRoot_FP hn)
    (mem_FP_pair (HM.replicate_mem_FP true) (mem_FP_pair HL.bits_mem_FP HR.bits_mem_FP))

def matchTable (initial : ℕ) (q : List Bool):=WordList.encode
  ((List.range (creating initial q)).map (fun i=>pair (BinaryNatCode.encode i) (BinaryNatCode.encode i)))

theorem matchTable_FP {initial : List Bool→ℕ} {q : List Bool→List Bool}
    (hi : UnaryFn initial) (hq : q∈FP) : (fun z=>matchTable (initial z) (q z))∈FP :=by
  have HE:=mem_FP_pair (mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP
    (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE ((creating_unary hi hq).replicate_mem_FP true))
  intro z
  simp only [matchTable,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    pairSnd_pair,List.length_replicate]

theorem matchTable_count (initial : ℕ) (q : List Bool) :
    WordListRecords.count (matchTable initial q)=creating initial q :=by
  simp only [matchTable,WordListRecords.count_encode,List.length_map,List.length_range]

theorem matchTable_lookup (initial : ℕ) (q : List Bool) (i : ℕ) (hi : i<creating initial q) :
    WordList.get (matchTable initial q) i=pair (BinaryNatCode.encode i) (BinaryNatCode.encode i) :=by
  simp only [matchTable,WordList.get_encode,List.getElem?_map,List.getElem?_range hi,
    Option.map_some,Option.getD_some]

def HintGood (n initial B : ℕ) (z : List Bool) : Prop :=
  0<count (pairFst z) ∧
  IntegralMixedChronologicalFrameCode.Good n (creating initial (pairFst z)) (labels (pairFst z)) ∧
  Nat.fromBitsLE (field 0 z)<3 ∧
  WordListRecords.count (labels (pairFst z))+1≤Nat.fromBitsLE (field 1 z) ∧
  Nat.fromBitsLE (field 1 z)<n+1 ∧
  Nat.fromBitsLE (field 2 z)≤2^B ∧ Nat.fromBitsLE (field 3 z)≤2^B ∧
  producer false (pairFst z)<creating initial (pairFst z) ∧
  producer true (pairFst z)<creating initial (pairFst z)

theorem hintGood_FP {n initial B : List Bool→ℕ} (hn : UnaryFn n) (hi : UnaryFn initial) (hB : UnaryFn B) :
    FPPred (fun z=>HintGood (n z) (initial z) (B z) z) :=by
  have HL:=mem_FP_comp pairFst_mem_FP labels_FP
  have HM:=BinaryFn.ofUnary (creating_unary hi pairFst_mem_FP)
  have HG:=(BinaryFn.ofUnary (WordListRecords.count_unary.comp HL)).add (BinaryFn.const 1)
  have HP:=(BinaryFn.const 2).powUnary hB
  have Hleft : BinaryFn (fun z=>producer false (pairFst z)):=(producer_binary false).comp pairFst_mem_FP
  have Hright : BinaryFn (fun z=>producer true (pairFst z)):=(producer_binary true).comp pairFst_mem_FP
  exact ((BinaryFn.const 0).lt (BinaryFn.ofUnary (count_unary.comp pairFst_mem_FP))).and
    ((IntegralMixedChronologicalFrameCode.good_FP hn HM HL).and
    (((field_binary 0).lt (BinaryFn.const 3)).and
    ((HG.le (field_binary 1)).and
    (((field_binary 1).lt ((BinaryFn.ofUnary hn).add (BinaryFn.const 1))).and
    (((field_binary 2).le HP).and (((field_binary 3).le HP).and
    ((Hleft.lt HM).and (Hright.lt HM))))))))

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbePacket

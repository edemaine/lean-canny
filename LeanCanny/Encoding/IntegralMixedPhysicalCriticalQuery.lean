/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedNative
public import LeanCanny.Encoding.IntegralMixedCriticalRecordConstructor
/-! # An original record reserves one normalized physical critical probe

The probe is appended before allocating either complete word. Parent and child
therefore use the same prepared root, radius, width and horizon. Endpoint labels
are chronological retained-bank indices, not arbitrary supplied real numbers.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalQuery
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def normalize (code : List Bool) := IntegralMixedCriticalRecordConstructor.word
  (Nat.fromBitsLE (IntegralMixedUnitRecordCode.field code 1))
  (Nat.fromBitsLE (IntegralMixedUnitRecordCode.field code 3))
  (Nat.fromBitsLE (IntegralMixedUnitRecordCode.field code 3))
  (IntegralMixedUnitRecordCode.field code 6) (IntegralMixedUnitRecordCode.field code 14)
  (IntegralMixedUnitRecordCode.field code 12)

theorem normalize_FP : normalize∈FP := IntegralMixedCriticalRecordConstructor.word_FP
  (BinaryFn.fromBits (IntegralMixedCommandHeaderBits.get_FP 1))
  (BinaryFn.fromBits (IntegralMixedCommandHeaderBits.get_FP 3))
  (BinaryFn.fromBits (IntegralMixedCommandHeaderBits.get_FP 3))
  (IntegralMixedCommandHeaderBits.get_FP 6) (IntegralMixedCommandHeaderBits.get_FP 14)
  (IntegralMixedCommandHeaderBits.get_FP 12)

def snoc (p : List Bool) := WordList.encode (WordListRecords.decode (pairFst p)++[pairSnd p])
private def entry (p : List Bool) := pair (WordList.get (pairFst p) (pairSnd p).length) []

theorem snoc_FP : snoc∈FP := by
  have E : entry∈FP := mem_FP_pair
    (mem_FP_of_eq (mem_FP_comp (WordListRecords.indexPacket_FP) WordList.reader_FP)
      (fun p=>by simp only [Function.comp_apply,WordListRecords.indexPacket,WordList.reader,pairFst_pair,pairSnd_pair,
        BinaryNatCode.encode,Nat.fromBitsLE_bits])) (constFn_mem_FP [])
  have H:=mem_FP_comp pairFst_mem_FP
    (flatMap_range_mem_FP E (WordListRecords.count_unary.replicate_mem_FP true))
  apply mem_FP_of_eq (appendFn_mem_FP H (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP [])))
  intro p
  simp only [snoc,WordListRecords.decode,FrozenCoordinatePermutationBits.encode_flatMap,
    List.flatMap_append,List.flatMap_map,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    entry,pairFst_pair,pairSnd_pair,List.length_replicate,Function.comp_apply]

theorem snoc_encode (ws : List (List Bool)) (v : List Bool) :
    snoc (pair (WordList.encode ws) v)=WordList.encode (ws++[v]) := by
  simp only [snoc,pairFst_pair,pairSnd_pair,WordListRecords.decode_encode]

/-- Input is the old context paired with the original critical record. -/
def prepare (p : List Bool) := pair (pairFst (pairFst p))
  (pair (snoc (pair (IntegralMixedCausalRecordPlanBits.records (pairFst p)) (normalize (pairSnd p))))
    (pairSnd (pairSnd (pairFst p))))

attribute [local irreducible] snoc normalize prepare

theorem prepare_FP : prepare∈FP := by
  have E:=mem_FP_pair (mem_FP_comp pairFst_mem_FP IntegralMixedCausalRecordPlanBits.records_FP)
    (mem_FP_comp pairSnd_mem_FP normalize_FP)
  have HS:=mem_FP_comp (f:=fun p=>pair (IntegralMixedCausalRecordPlanBits.records (pairFst p))
    (normalize (pairSnd p))) (g:=snoc) E snoc_FP
  have HH:=mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HT:=mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  exact mem_FP_of_eq (mem_FP_pair HH (mem_FP_pair HS HT)) (fun p=>by rw [prepare];rfl)

theorem prepare_candidate (ctx code : List Bool) : pairFst (prepare (pair ctx code))=pairFst ctx := by
  simp only [prepare,pairFst_pair]
theorem prepare_records (ctx code : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (prepare (pair ctx code))=
      WordList.encode (WordListRecords.decode (IntegralMixedCausalRecordPlanBits.records ctx)++[normalize code]) := by
  simp only [prepare,IntegralMixedCausalRecordPlanBits.records,pairFst_pair,pairSnd_pair,snoc]
theorem prepare_count (ctx code : List Bool) :
    IntegralMixedCausalRecordPlanBits.count (prepare (pair ctx code))=
      IntegralMixedCausalRecordPlanBits.count ctx+1 := by
  unfold IntegralMixedCausalRecordPlanBits.count
  rw [prepare_records,WordListRecords.count_encode,List.length_append,WordListRecords.length_decode]
  rfl

/-- Query: prepared root, fixed parent full word, left/right chronological labels. -/
def root (q : List Bool) := pairFst q
def parentWord (q : List Bool) := pairFst (pairSnd q)
def leftWord (q : List Bool) := pairFst (pairSnd (pairSnd (pairSnd (root q))))
def rightWord (q : List Bool) := pairSnd (pairSnd (pairSnd (pairSnd (root q))))
def lastCode (q : List Bool) := WordList.get (IntegralMixedCausalRecordPlanBits.records (root q))
  (IntegralMixedCausalRecordPlanBits.count (root q)-1)
def critical (q : List Bool) : Prop :=
  0<IntegralMixedCausalRecordPlanBits.count (root q) ∧
  IntegralMixedUnitRecordCode.critical (lastCode q)=true ∧
  IntegralMixedUnitRecordCode.field (lastCode q) 3=IntegralMixedUnitRecordCode.field (lastCode q) 4

theorem lastCode_FP : lastCode∈FP := by
  have H:=mem_FP_comp (mem_FP_pair
    (mem_FP_comp pairFst_mem_FP IntegralMixedCausalRecordPlanBits.records_FP)
    (BinaryFn.ofUnary (((IntegralMixedCausalRecordPlanBits.count_unary).comp pairFst_mem_FP).sub (UnaryFn.const 1))).bits_mem_FP)
    WordList.reader_FP
  exact mem_FP_of_eq H (fun q=>by simp only [Function.comp_apply,lastCode,root,WordList.reader,
    pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits])

theorem critical_FP : FPPred critical := by
  have HC:=((BinaryFn.const 0).lt (BinaryFn.ofUnary (IntegralMixedCausalRecordPlanBits.count_unary.comp pairFst_mem_FP)))
  have HF:=(FPPred.getBit (mem_FP_comp lastCode_FP (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0))
  have HE:=Brackets.stringEq_fppred (mem_FP_comp lastCode_FP (IntegralMixedCommandHeaderBits.get_FP 3))
    (mem_FP_comp lastCode_FP (IntegralMixedCommandHeaderBits.get_FP 4))
  exact (HC.and (HF.and HE)).of_iff (fun _=>Iff.rfl)

theorem normalize_critical (code : List Bool) : IntegralMixedUnitRecordCode.critical (normalize code)=true := by
  simp only [IntegralMixedUnitRecordCode.critical,normalize,IntegralMixedCriticalRecordConstructor.word,
    IntegralMixedUnitRecordCode.field,WordList.get_encode,List.getElem?_cons_zero,Option.getD_some]

theorem normalize_objective (code : List Bool) :
    IntegralMixedUnitRecordCode.field (normalize code) 3=IntegralMixedUnitRecordCode.field (normalize code) 4 := by
  simp only [normalize,IntegralMixedCriticalRecordConstructor.word,IntegralMixedUnitRecordCode.field,
    WordList.get_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]

def withEndpoints (ctx : List Bool) (a b : ℕ) :=pair (pairFst ctx)
  (pair (IntegralMixedCausalRecordPlanBits.records ctx)
    (pair (pairSnd (pairSnd ctx)) (pair (BinaryNatCode.encode a) (BinaryNatCode.encode b))))

attribute [local irreducible] withEndpoints

theorem withEndpoints_FP {ctx : List Bool→List Bool} {a b : List Bool→ℕ}
    (hc : ctx∈FP) (ha : BinaryFn a) (hb : BinaryFn b) :
    (fun q=>withEndpoints (ctx q) (a q) (b q))∈FP :=by
  have HF:=mem_FP_comp (f:=ctx) (g:=pairFst) hc pairFst_mem_FP
  have HR:=mem_FP_comp (f:=ctx) (g:=IntegralMixedCausalRecordPlanBits.records) hc
    IntegralMixedCausalRecordPlanBits.records_FP
  have HT:=mem_FP_comp (f:=ctx) (g:=fun q=>pairSnd (pairSnd q)) hc
    (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact mem_FP_of_eq (mem_FP_pair HF (mem_FP_pair HR (mem_FP_pair HT
    (mem_FP_pair ha.bits_mem_FP hb.bits_mem_FP)))) (fun _=>by rw [withEndpoints];rfl)

def packet (ctx code w : List Bool) (a b : ℕ) :=
  pair (prepare (pair (withEndpoints ctx a b) code)) (pair w [])

attribute [local irreducible] packet

theorem packet_FP {ctx code w : List Bool→List Bool} {a b : List Bool→ℕ}
    (hc : ctx∈FP) (hd : code∈FP) (hw : w∈FP) (ha : BinaryFn a) (hb : BinaryFn b) :
    (fun q=>packet (ctx q) (code q) (w q) (a q) (b q))∈FP :=by
  have HE:=withEndpoints_FP hc ha hb
  have HP:=mem_FP_pair HE hd
  have HR:=mem_FP_comp (f:=fun q=>pair (withEndpoints (ctx q) (a q) (b q)) (code q))
    (g:=prepare) HP prepare_FP
  exact mem_FP_of_eq (mem_FP_pair HR (mem_FP_pair hw (constFn_mem_FP []))) (fun _=>by rw [packet];rfl)

theorem lastCode_packet (ctx code w : List Bool) (a b : ℕ) :
    lastCode (packet ctx code w a b)=normalize code := by
  simp only [lastCode,packet,root,pairFst_pair,prepare_count,Nat.add_sub_cancel]
  rw [prepare_records,WordList.get_encode]
  have HE : IntegralMixedCausalRecordPlanBits.count (withEndpoints ctx a b)=
      (WordListRecords.decode (IntegralMixedCausalRecordPlanBits.records (withEndpoints ctx a b))).length :=
    (WordListRecords.length_decode _).symm
  rw [HE,List.getElem?_append_right (by omega),Nat.sub_self]
  rfl

theorem critical_packet (ctx code w : List Bool) (a b : ℕ) : critical (packet ctx code w a b) := by
  refine ⟨?_,?_,?_⟩
  · simp only [packet,root,pairFst_pair,prepare_count]
    omega
  · rw [lastCode_packet]
    exact normalize_critical code
  · rw [lastCode_packet]
    exact normalize_objective code

theorem normalize_data {n birth : ℕ} (d : IntegralMixedCriticalRecordConstructor.Data n birth)
    (hc : d.coordinate.val=d.objective.val) : normalize d.code=d.code := by
  unfold normalize
  rw [IntegralMixedCriticalRecordConstructor.field_1,
    IntegralMixedCriticalRecordConstructor.field_3,IntegralMixedCriticalRecordConstructor.field_6,
    IntegralMixedCriticalRecordConstructor.field_14,IntegralMixedCriticalRecordConstructor.field_12]
  simp only [BinaryNatCode.encode,Nat.fromBitsLE_bits,IntegralMixedCriticalRecordConstructor.Data.code,hc]

theorem left_packet (ctx code w : List Bool) (a b : ℕ) : leftWord (packet ctx code w a b)=BinaryNatCode.encode a := by
  simp only [leftWord,root,packet,prepare,withEndpoints,pairFst_pair,pairSnd_pair]
theorem right_packet (ctx code w : List Bool) (a b : ℕ) : rightWord (packet ctx code w a b)=BinaryNatCode.encode b := by
  simp only [rightWord,root,packet,prepare,withEndpoints,pairFst_pair,pairSnd_pair]

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalQuery

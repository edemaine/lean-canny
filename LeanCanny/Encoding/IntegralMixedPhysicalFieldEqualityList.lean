/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
public import LeanCanny.Encoding.WordListRecords
/-! # A native finite list of retained-field pairs shares two full words -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalFieldEquality (sample context word)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def table (z : List Bool) :=pairSnd (pairSnd z)
def count (z : List Bool) :=WordListRecords.count (table z)
theorem count_unary : UnaryFn count:=WordListRecords.count_unary.comp (show table∈FP by polytime [table])
def field (r : List Bool) :=WordList.reader (pair (table (pairFst r)) (BinaryNatCode.encode (pairSnd r).length))
theorem field_FP : field∈FP:=mem_FP_comp (mem_FP_pair (by polytime [table])
  (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP
def label (right : Bool) (code : List Bool) :=Nat.fromBitsLE (if right then pairSnd code else pairFst code)
theorem label_binary (right : Bool) : BinaryFn (label right):=by
  cases right <;> exact BinaryFn.fromBits (by polytime)
def packet (cL wL cR wR code : List Bool) :=pair (pair cL wL) (pair (pair cR wR) code)
def query (r : List Bool) :=IntegralMixedPhysicalFieldEquality.packet
  (context false (pairFst r)) (word false (pairFst r)) (context true (pairFst r)) (word true (pairFst r))
  (label false (field r)) (label true (field r))
attribute [local irreducible] field label
theorem query_FP : query∈FP:=by
  unfold query IntegralMixedPhysicalFieldEquality.packet
  have HL : BinaryFn (label false∘field):=(label_binary false).comp field_FP
  have HR : BinaryFn (label true∘field):=(label_binary true).comp field_FP
  have HS (right : Bool) : (fun r=>sample right (pairFst r))∈FP:=by
    cases right <;> polytime [sample]
  have HC (right : Bool) : (fun r=>context right (pairFst r))∈FP:=
    mem_FP_comp (HS right) pairFst_mem_FP
  have HW (right : Bool) : (fun r=>word right (pairFst r))∈FP:=
    mem_FP_comp (HS right) pairSnd_mem_FP
  exact mem_FP_pair
    (mem_FP_pair (HC false) (HW false))
    (mem_FP_pair
      (mem_FP_pair (HC true) (HW true))
      (mem_FP_pair HL.bits_mem_FP HR.bits_mem_FP))
theorem query_packet (cL wL cR wR code : List Bool) (i : ℕ) :
    query (pair (packet cL wL cR wR code) (List.replicate i true))=
      IntegralMixedPhysicalFieldEquality.packet cL wL cR wR
        (label false (WordList.get code i)) (label true (WordList.get code i)) :=by
  simp only [query,field,table,context,word,sample,packet,Bool.false_eq_true,ite_false,ite_true,
    pairFst_pair,pairSnd_pair,List.length_replicate,WordList.reader_packet]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "S" => IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

noncomputable def holds (z : List Bool) : Prop:=∀i<count z,
  query (pair z (List.replicate i true))∈IntegralMixedPhysicalFieldEquality.language hn ht ha hR
theorem holds_evaluator : SpaceFunction (fun z=>[decide (holds hn ht ha hR z)]) :=by
  have E:=((IntegralMixedPhysicalFieldEquality.decider hn ht ha hR).precompose query query_FP).flagEvaluator
  exact (E.forall_unary count_unary).congr (funext fun z=>by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [holds,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq])
noncomputable def language : Language:={z |SquareSampleCompleteVertices.Valid S (context false z) (word false z) ∧
  SquareSampleCompleteVertices.Valid S (context true z) (word true z) ∧holds hn ht ha hR z}
theorem decider : SpaceDecider (language hn ht ha hR) :=by
  have EV (right : Bool):=((SquareSampleCompleteVertices.decider (IntegralMixedPhysicalMarkedNative.access hn ht ha hR false)).precompose
    (sample right) (IntegralMixedPhysicalFieldEquality.sample_FP right)).flagEvaluator
  apply ((EV false).andFlags ((EV true).andFlags (holds_evaluator hn ht ha hR))).decider
    (fun v=>decide (v=[true])) (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro z
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,Set.mem_preimage,context,word,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language hn ht ha hR∈PSPACE:=(decider hn ht ha hR).mem_PSPACE

theorem holds_packet_iff (cL wL cR wR code : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR)
    (hb : ∀i<WordListRecords.count code,
      label false (WordList.get code i)<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cL ∧
      label true (WordList.get code i)<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cR) :
    holds hn ht ha hR (packet cL wL cR wR code) ↔
      ∀i<WordListRecords.count code,
        IntegralMixedPhysicalFieldEquality.point hn ht ha hR cL wL hL (label false (WordList.get code i))=
          IntegralMixedPhysicalFieldEquality.point hn ht ha hR cR wR hR' (label true (WordList.get code i)) :=by
  simp only [holds]
  simp_rw [query_packet]
  simp only [count,table,packet,pairSnd_pair]
  constructor
  · intro H i hi
    exact (IntegralMixedPhysicalFieldEquality.language_packet_iff hn ht ha hR cL wL cR wR hL hR' _ _ (hb i hi).1 (hb i hi).2).mp (H i hi)
  · intro H i hi
    exact (IntegralMixedPhysicalFieldEquality.language_packet_iff hn ht ha hR cL wL cR wR hL hR' _ _ (hb i hi).1 (hb i hi).2).mpr (H i hi)

theorem language_packet_iff (cL wL cR wR code : List Bool)
    (hL : SquareSampleCompleteVertices.Valid S cL wL) (hR' : SquareSampleCompleteVertices.Valid S cR wR)
    (hb : ∀i<WordListRecords.count code,
      label false (WordList.get code i)<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cL ∧
      label true (WordList.get code i)<IntegralMixedPhysicalFieldEquality.count hn ht ha hR cR) :
    packet cL wL cR wR code∈language hn ht ha hR ↔
      ∀i<WordListRecords.count code,
        IntegralMixedPhysicalFieldEquality.point hn ht ha hR cL wL hL (label false (WordList.get code i))=
          IntegralMixedPhysicalFieldEquality.point hn ht ha hR cR wR hR' (label true (WordList.get code i)) :=by
  have HM : packet cL wL cR wR code∈language hn ht ha hR ↔holds hn ht ha hR (packet cL wL cR wR code) :=by
    constructor
    · exact fun h=>h.2.2
    · intro h
      refine ⟨?_,?_,h⟩
      · simpa only [context,word,sample,packet,Bool.false_eq_true,ite_false,pairFst_pair,pairSnd_pair] using hL
      · simpa only [context,word,sample,packet,ite_true,pairFst_pair,pairSnd_pair] using hR'
  exact HM.trans (holds_packet_iff hn ht ha hR cL wL cR wR code hL hR' hb)

end LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityList

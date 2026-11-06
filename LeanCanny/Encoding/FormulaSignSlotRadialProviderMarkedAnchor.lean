/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCrossPoint
/-! # Native attachment to the own initial marked point

Every coordinate of the current point is compared with its literal initial
prelude field, using the same accepted full word on both sides of the scan.
This checker asserts point equality, not membership in a connected component.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedAnchor
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "D" => FormulaSignSlotRadialProviderAtomic.dimension
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "C" => FormulaSignSlotRadialProviderAtomic.context
local notation "W" => FormulaSignSlotRadialProviderAtomic.word
local notation "full" => FormulaSignSlotRadialProviderAtomic.full_valid
local notation "sig" => FormulaSignSlotRadialProviderIdentity.ownSignature
local notation "n" => FormulaSignSlotRadialExternalPrelude.number

noncomputable def initialSignature (q : List Bool) := WordList.encode
  ((List.range (D q+1)).map BinaryNatCode.encode)

theorem initialSignature_FP : initialSignature∈FP := by
  apply mem_FP_of_eq (flatMap_range_mem_FP
    (mem_FP_pair (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP (constFn_mem_FP []))
    ((FormulaSignSlotRadialProviderAtomic.dimension_unary.add (UnaryFn.const 1)).replicate_mem_FP true))
  intro q
  simp only [initialSignature,FrozenCoordinatePermutationBits.encode_flatMap,List.flatMap_map,
    pairSnd_pair,List.length_replicate]

noncomputable def table (q : List Bool) :=
  IntegralMixedPhysicalPointSignatureComparison.pairs (D q) (sig q) (initialSignature q)
noncomputable def query (q : List Bool) := FormulaSignSlotRadialProviderFieldEqualityList.packet
  (C q) (W q) (C q) (W q) (table q)

theorem table_FP : table∈FP := IntegralMixedPhysicalPointSignatureComparison.pairs_FP
  FormulaSignSlotRadialProviderAtomic.dimension_unary FormulaSignSlotRadialProviderAtomic.native_signature initialSignature_FP

theorem query_FP : query∈FP := mem_FP_pair
  (mem_FP_pair FormulaSignSlotRadialProviderAtomic.context_FP FormulaSignSlotRadialProviderAtomic.word_FP)
  (mem_FP_pair (mem_FP_pair FormulaSignSlotRadialProviderAtomic.context_FP FormulaSignSlotRadialProviderAtomic.word_FP) table_FP)

noncomputable def language : Language := {q | A q∧query q∈FormulaSignSlotRadialProviderFieldEqualityList.language}

theorem decider : SpaceDecider language := by
  have E:=(FormulaSignSlotRadialProviderFieldEqualityList.decider.precompose query query_FP).flagEvaluator
  apply (FormulaSignSlotRadialProviderAtomic.evaluator.andFlags E).decider (fun v=>decide (v=[true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language,Set.mem_ofPred_eq,Set.mem_preimage,List.cons.injEq,and_true,decide_eq_true_eq]

theorem mem_PSPACE : language∈PSPACE := decider.mem_PSPACE

theorem dimension_eq (q : List Bool) : D q+1=n (FormulaSignSlotRadialProviderAtomic.provider q)+4 := by
  have H:=FormulaSignSlotRadialProviderIdentity.dimension_eq q
  change D q=n (FormulaSignSlotRadialProviderAtomic.provider q)+3 at H
  omega

theorem initial_bounded (q : List Bool) (i : Fin (D q+1)) :
    i.val<FormulaSignSlotRadialProviderFieldEquality.count (C q) := by
  have HI:=FormulaSignSlotRadialProviderAtomic.initial_eq q
  have HC : FormulaSignSlotRadialProviderFieldEquality.count (C q)=
      FormulaSignSlotRadialProviderAtomic.initial q+
        IntegralMixedCausalRecordPlanBits.count (FormulaSignSlotRadialProviderAtomic.root q) := by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    simp only [FormulaSignSlotRadialProviderAtomic.context,pairFst_pair]
    rfl
  have HB:=i.isLt
  omega

theorem table_count (q : List Bool) : WordListRecords.count (table q)=D q+1 :=
  IntegralMixedPhysicalPointSignatureComparison.pairs_count _ _ _

theorem table_lookup (q : List Bool) (i : Fin (D q+1)) :
    WordList.get (table q) i.val=pair (WordList.get (sig q) i.val) (BinaryNatCode.encode i.val) := by
  rw [table,IntegralMixedPhysicalPointSignatureComparison.pairs_lookup]
  simp only [initialSignature,WordList.get_encode,List.getElem?_map,List.getElem?_range i.isLt,
    Option.map_some,Option.getD_some]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family

theorem initial_point (q : List Bool) (hv : A q) (i : Fin (D q+1)) :
    FormulaSignSlotRadialProviderFieldEquality.point (C q) (W q) (full q hv) i.val=
      FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv (Fin.cast (dimension_eq q) i) := by
  simpa only [FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint,
    FormulaSignSlotRadialProviderAtomic.field,Fin.val_cast] using
    FormulaSignSlotRadialProviderFieldEquality.point_env (C q) (W q) (full q hv) i.val (initial_bounded q i)

private theorem fin_heq_iff {a b : ℕ} (H : a=b) (p : Fin a→ℝ) (q : Fin b→ℝ) :
    HEq p q↔∀i,p i=q (Fin.cast H i) := by
  cases H
  constructor
  · intro HE i
    exact congrFun (eq_of_heq HE) i
  · intro HE
    exact heq_of_eq (funext HE)

attribute [local irreducible] FormulaSignSlotRadialProviderAtomic.dimension
  FormulaSignSlotRadialProviderAtomic.initial FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderAtomic.context FormulaSignSlotRadialProviderAtomic.word
  FormulaSignSlotRadialProviderIdentity.point FormulaSignSlotRadialProviderIdentity.ownSignature
  FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint
  FormulaSignSlotRadialProviderFieldEquality.point FormulaSignSlotRadialProviderFieldEquality.count
  IntegralFramedPhysicalSquare.input table query

/-- The finite native scan compares the entire current point with the initial
marked vector. No depth restriction or geometric attachment premise is used. -/
theorem query_iff (q : List Bool) (hv : A q) :
    query q∈FormulaSignSlotRadialProviderFieldEqualityList.language ↔
      HEq (FormulaSignSlotRadialProviderIdentity.point q hv)
        (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv) := by
  have HB : ∀i<WordListRecords.count (table q),
      FormulaSignSlotRadialProviderFieldEqualityList.label false (WordList.get (table q) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (C q) ∧
      FormulaSignSlotRadialProviderFieldEqualityList.label true (WordList.get (table q) i)<
        FormulaSignSlotRadialProviderFieldEquality.count (C q) := by
    intro i hi
    rw [table_count] at hi
    rw [table_lookup q ⟨i,hi⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact ⟨FormulaSignSlotRadialProviderIdentity.signature_bound q hv ⟨i,hi⟩,initial_bounded q ⟨i,hi⟩⟩
  unfold query
  rw [FormulaSignSlotRadialProviderFieldEqualityList.language_packet_iff
    _ _ _ _ _ (full q hv) (full q hv) HB,fin_heq_iff (dimension_eq q)]
  constructor
  · intro HE i
    have H:=HE i.val (by rw [table_count];exact i.isLt)
    rw [table_lookup q i] at H
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits] at H
    exact (FormulaSignSlotRadialProviderIdentity.signature_point q hv i).symm.trans (H.trans (initial_point q hv i))
  · intro HE i hi
    rw [table_count] at hi
    rw [table_lookup q ⟨i,hi⟩]
    simp only [FormulaSignSlotRadialProviderFieldEqualityList.label,Bool.false_eq_true,ite_false,ite_true,
      pairFst_pair,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
    exact (FormulaSignSlotRadialProviderIdentity.signature_point q hv ⟨i,hi⟩).trans
      ((HE ⟨i,hi⟩).trans (initial_point q hv ⟨i,hi⟩).symm)

theorem language_iff (q : List Bool) (hv : A q) : q∈language ↔
    HEq (FormulaSignSlotRadialProviderIdentity.point q hv)
      (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv) := by
  simpa only [language,Set.mem_ofPred_eq,hv,true_and] using query_iff q hv

theorem language_native_iff (q : List Bool) (hv : A q) : q∈language ↔
    HEq (FormulaSignSlotRadialProviderAtomic.point q hv)
      (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv) := by
  rw [language_iff q hv]
  constructor
  · intro H
    exact (FormulaSignSlotRadialProviderCrossPoint.point_native_heq q hv).symm.trans H
  · intro H
    exact (FormulaSignSlotRadialProviderCrossPoint.point_native_heq q hv).trans H


theorem mem_iff (q : List Bool) : q∈language ↔
    ∃hv : A q,HEq (FormulaSignSlotRadialProviderAtomic.point q hv)
      (FormulaSignSlotRadialProviderAtomic.MarkedPrelude.preludePoint q hv) := by
  constructor
  · intro H
    exact ⟨H.1,(language_native_iff q H.1).mp H⟩
  · rintro ⟨hv,H⟩
    exact (language_native_iff q hv).mpr H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedAnchor

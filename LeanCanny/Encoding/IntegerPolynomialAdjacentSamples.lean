/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialAlgebraicCut
public import LeanCanny.Geometry.OrderedRealCellRank

/-! # Native adjacency of independently labeled algebraic samples

Two complete scalar labels represent an endpoint and a candidate sample.
Root counts below the two values and zero-count tests recognize precisely
the gap immediately to the endpoint's left or right. Every label is checked;
the three polynomial sources need only native coefficients and binary bounds.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialAdjacentSamples
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegerPolynomialRootQueriesBits (Source)
open Geometry.OrderedRealCells
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def endpointRecord (q : List Bool) : List Bool := pair
  (pair (pairFst (pairFst q)) (pairSnd (pairFst q))) []
def sampleRecord (q : List Bool) : List Bool := pair (pair (pairFst (pairFst q)) (pairSnd q)) []
theorem endpointRecord_FP : endpointRecord ∈ FP := by polytime [endpointRecord]
theorem sampleRecord_FP : sampleRecord ∈ FP := by polytime [sampleRecord]

noncomputable def numeric (S T Q : Source) (right : Bool) (q : List Bool) : Prop :=
  0 < IntegerPolynomialAlgebraicCut.zeroCount S Q (endpointRecord q) ∧
    IntegerPolynomialAlgebraicCut.zeroCount T Q (sampleRecord q) = 0 ∧
      IntegerPolynomialAlgebraicCut.count T Q (sampleRecord q) =
        IntegerPolynomialAlgebraicCut.count S Q (endpointRecord q) + if right then 1 else 0

noncomputable def language (S T Q : Source) (right : Bool) : Language :=
  {q | endpointRecord q ∈ IntegerPolynomialSampleSlice.valid S ∧
    sampleRecord q ∈ IntegerPolynomialSampleSlice.valid T ∧ numeric S T Q right q}

def compare (right : Bool) (z : List Bool) : Bool := decide
  (0 < Nat.fromBitsLE (pairFst (pairSnd z)) ∧ Nat.fromBitsLE (pairSnd (pairSnd z)) = 0 ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) = Nat.fromBitsLE (pairFst (pairFst z)) + if right then 1 else 0)

theorem compare_FP (right : Bool) : (fun z => [compare right z]) ∈ FP := by
  have ha := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have ht := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have hza := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hzt := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact (((BinaryFn.const 0).lt hza).and ((hzt.eq (BinaryFn.const 0)).and
    (ht.eq (ha.add (BinaryFn.const (if right then 1 else 0)))))).flag_mem_FP

theorem numericDecider {S T Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access T) (C : IntegerPolynomialRootQueriesBits.Access Q) (right : Bool) :
    SpaceDecider {q | numeric S T Q right q} := by
  have E := (IntegerPolynomialAlgebraicCut.evaluator A C).precompose endpointRecord endpointRecord_FP
  have F := (IntegerPolynomialAlgebraicCut.evaluator B C).precompose sampleRecord sampleRecord_FP
  have G := (IntegerPolynomialAlgebraicCut.zeroEvaluator A C).precompose endpointRecord endpointRecord_FP
  have H := (IntegerPolynomialAlgebraicCut.zeroEvaluator B C).precompose sampleRecord sampleRecord_FP
  apply ((E.pairOutputs F).pairOutputs (G.pairOutputs H)).decider (compare right) (compare_FP right)
  intro q
  simp only [numeric, Set.mem_ofPred_eq, compare, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem decider {S T Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access T) (C : IntegerPolynomialRootQueriesBits.Access Q) (right : Bool) :
    SpaceDecider (language S T Q right) := by
  have V := ((IntegerPolynomialSampleSlice.validDecider A).precompose endpointRecord endpointRecord_FP).flagEvaluator
  have W := ((IntegerPolynomialSampleSlice.validDecider B).precompose sampleRecord sampleRecord_FP).flagEvaluator
  have N := (numericDecider A B C right).flagEvaluator
  apply (V.andFlags (W.andFlags N)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {S T Q : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    (B : IntegerPolynomialRootQueriesBits.Access T) (C : IntegerPolynomialRootQueriesBits.Access Q) (right : Bool) :
    language S T Q right ∈ PSPACE := (decider A B C right).mem_PSPACE

theorem language_iff (S T Q : Source) (right : Bool) (q : List Bool)
    (ha : endpointRecord q ∈ IntegerPolynomialSampleSlice.valid S)
    (ht : sampleRecord q ∈ IntegerPolynomialSampleSlice.valid T) : q ∈ language S T Q right ↔
    IntegerPolynomialSampleSlice.point S (endpointRecord q) ∈ IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q)) ∧
      IntegerPolynomialSampleSlice.point T (sampleRecord q) ∉ IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q)) ∧
        lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q)))
          (IntegerPolynomialSampleSlice.point T (sampleRecord q)) =
        lowerCount (IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q)))
          (IntegerPolynomialSampleSlice.point S (endpointRecord q)) + if right then 1 else 0 := by
  simp only [language, Set.mem_ofPred_eq, ha, ht, true_and, numeric]
  rw [IntegerPolynomialAlgebraicCut.zeroCount_pos_iff S Q _ ha,
    IntegerPolynomialAlgebraicCut.zeroCount_eq_zero_iff T Q _ ht,
    IntegerPolynomialAlgebraicCut.count_below T Q _ ht, IntegerPolynomialAlgebraicCut.count_below S Q _ ha]
  simp only [endpointRecord, sampleRecord, pairFst_pair, lowerCount]

theorem gap_packet (S T Q : Source) (right : Bool) (q : List Bool)
    (ha : endpointRecord q ∈ IntegerPolynomialSampleSlice.valid S)
    (ht : sampleRecord q ∈ IntegerPolynomialSampleSlice.valid T)
    (i : Fin (IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q))).card)
    (hi : root (IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q))) i =
      IntegerPolynomialSampleSlice.point S (endpointRecord q)) :
    q ∈ language S T Q right ↔ IntegerPolynomialSampleSlice.point T (sampleRecord q) ∈
      gap (IntegerPolynomialRootQueriesBits.rootSet Q (pairFst (pairFst q)))
        (if right then rightGap _ i else leftGap _ i) := by
  rw [language_iff S T Q right q ha ht, ← hi]
  simp only [root_mem, true_and]
  cases right
  · simpa only [Bool.false_eq_true, ite_false, Nat.add_zero] using
      (mem_leftGap_iff_rank _ i (IntegerPolynomialSampleSlice.point T (sampleRecord q))).symm
  · simpa only [ite_true] using
      (mem_rightGap_iff_rank _ i (IntegerPolynomialSampleSlice.point T (sampleRecord q))).symm

end LeanCanny.Encoding.IntegerPolynomialAdjacentSamples

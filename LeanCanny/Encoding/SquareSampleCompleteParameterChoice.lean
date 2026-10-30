/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteParameterEquality
public import LeanCanny.Encoding.IntegerPolynomialSampleSlicePoint
public import LeanCanny.Computation.BoundedChoice

/-! # Computing a scalar primitive-parameter record for a complete point

A native bounded search finds a fixed-width scalar root label whose Thom
signs agree with the parent point's primitive parameter. The output includes
an actual valid algebraic-slice record. Every recovered parent coordinate is
unchanged, including for singular roots of the original square system.
-/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleCompleteParameterChoice
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open SquareSampleCompleteParameterTest (source theta)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def width (F : Inputs) (u : List Bool) : ℕ :=
  SquareSampleCompleteVertices.width (IntegerPolynomialSampleInput.input (source F)) (pairFst u)
theorem width_unary {F : Inputs} (h : F.Access) : UnaryFn (width F) :=
  (IntegerPolynomialSampleInput.width_unary (SquareSampleCompleteParameterTest.sourceAccess h)).comp pairFst_mem_FP

noncomputable def word (F : Inputs) (q : List Bool) : List Bool :=
  ImplicitGraph.word (width F (pairFst q)) (Nat.fromBitsLE (pairSnd q))
theorem word_FP {F : Inputs} (h : F.Access) : word F ∈ FP :=
  ImplicitGraph.word_computable ((width_unary h).comp pairFst_mem_FP) (BinaryFn.fromBits pairSnd_mem_FP)
noncomputable def candidate (F : Inputs) (q : List Bool) : List Bool := pair (pairFst q) (word F q)
theorem candidate_FP {F : Inputs} (h : F.Access) : candidate F ∈ FP := mem_FP_pair pairFst_mem_FP (word_FP h)

noncomputable def language (F : Inputs) : Language := candidate F ⁻¹' SquareSampleCompleteParameterEquality.language F
theorem decider {F : Inputs} (h : F.Access) : SpaceDecider (language F) :=
  (SquareSampleCompleteParameterEquality.decider h).precompose (candidate F) (candidate_FP h)

noncomputable def bound (F : Inputs) (u : List Bool) : ℕ := 2 ^ width F u
theorem bound_binary {F : Inputs} (h : F.Access) : BinaryFn (bound F) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp (width_unary h)

theorem exists_candidate (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    ∃ k < bound F (pair c w), pair (pair c w) (BinaryNatCode.encode k) ∈ language F := by
  obtain ⟨v, hv⟩ := SquareSampleCompleteParameterEquality.label_exists F c w hw
  have hV : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (source F)) c v := by
    simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq,
      SquareSampleCompleteParameterEquality.scalarVertex, SquareSampleCompleteParameterEquality.origin,
      pairFst_pair, pairSnd_pair] using hv.2.1
  have hlen : v.length = width F (pair c w) := by
    simpa only [width, pairFst_pair, SquareSampleCompleteVertices.width] using (Classical.choose hV).1
  refine ⟨Nat.fromBitsLE v, ?_, ?_⟩
  · simpa only [bound, ← hlen] using Nat.fromBitsLE_lt_pow_length v
  · change candidate F (pair (pair c w) (BinaryNatCode.encode (Nat.fromBitsLE v))) ∈
      SquareSampleCompleteParameterEquality.language F
    have H : word F (pair (pair c w) (BinaryNatCode.encode (Nat.fromBitsLE v))) = v := by
      simp only [word, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      rw [← hlen, ImplicitGraph.word_fromBitsLE]
    simpa only [candidate, pairFst_pair, H] using hv

noncomputable def index (F : Inputs) (u : List Bool) : ℕ := BoundedChoice.search (language F) u (bound F u) - 1
noncomputable def value (F : Inputs) (u : List Bool) : List Bool := word F (pair u (BinaryNatCode.encode (index F u)))

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (value F) := by
  have E := BoundedChoice.evaluator (decider h) (fun u => BinaryNatCode.encode (bound F u)) (bound_binary h).bits_mem_FP
  exact (E.withInput.postcompose (word F) (word_FP h)).congr (funext fun u => by
    simp only [value, index, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem value_valid (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    pair (pair c w) (value F (pair c w)) ∈ SquareSampleCompleteParameterEquality.language F := by
  have H := BoundedChoice.witness (language F) (pair c w) (bound F (pair c w)) (exists_candidate F c w hw)
  have HH := H.2
  change candidate F (pair (pair c w) (BinaryNatCode.encode (BoundedChoice.search (language F) (pair c w) (bound F (pair c w)) - 1))) ∈
    SquareSampleCompleteParameterEquality.language F at HH
  simpa only [candidate, pairFst_pair, value, index] using HH

theorem scalar_valid (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (source F)) c (value F (pair c w)) := by
  have H := (value_valid F c w hw).2.1
  simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq,
    SquareSampleCompleteParameterEquality.scalarVertex, SquareSampleCompleteParameterEquality.origin,
    pairFst_pair, pairSnd_pair] using H

theorem value_packet (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (source F)) c (value F (pair c w))
      (scalar_valid F c w hw)).val (0 : Fin 1) = theta F c w :=
  ((SquareSampleCompleteParameterEquality.packet F c w _ hw (scalar_valid F c w hw)).mp (value_valid F c w hw)).symm

noncomputable def record (F : Inputs) (u : List Bool) : List Bool := pair (pair (pairFst u) (value F u)) []
theorem recordEvaluator {F : Inputs} (h : F.Access) : SpaceFunction (record F) := by
  have H := (evaluator h).withInput.postcompose (fun q => pair (pair (pairFst (pairFst q)) (pairSnd q)) [])
    (by polytime)
  exact H.congr (funext fun u => by simp only [record, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem record_valid (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    record F (pair c w) ∈ IntegerPolynomialSampleSlice.valid (source F) := by
  simpa only [record, pairFst_pair] using
    (IntegerPolynomialSampleSlice.valid_packet (source F) c (value F (pair c w)) []).mpr (scalar_valid F c w hw)

theorem record_point (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    IntegerPolynomialSampleSlice.point (source F) (record F (pair c w)) = theta F c w := by
  have H := IntegerPolynomialSampleSlice.point_packet (source F) c (value F (pair c w)) [] (scalar_valid F c w hw)
  simpa only [record, pairFst_pair] using H.trans (value_packet F c w hw)

theorem decode_record (F : Inputs) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    SquareSampleParameters.decode F c (IntegerPolynomialSampleSlice.point (source F) (record F (pair c w))) =
      (SquareSampleCompleteVertices.candidate F c w hw).val := by
  rw [record_point F c w hw]
  exact SquareSampleCompleteParameterTest.decode_theta F c w hw

end LeanCanny.Encoding.SquareSampleCompleteParameterChoice

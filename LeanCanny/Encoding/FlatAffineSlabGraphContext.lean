/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphCodes

/-! # Native slab context checks independent of spatial fiber nonemptiness

The frame, both endpoint/sample scalar pairs, and both original slab codes
are validated without requiring a spatial root at either sample. Empty
interior fibers and isolated endpoint components therefore remain admissible.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContext
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def adjacentQuery (side : Bool) (c : List Bool) : List Bool :=
  pair (pair (pairFst (source c)) (endpointWord side c)) (sampleWord side c)
def numericQuery (side : Bool) (c : List Bool) : List Bool :=
  pair (pair (source c) []) (pair (sampleWord side c) (gapWord c))
theorem adjacentQuery_FP (side : Bool) : adjacentQuery side ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp FlatAffineSlabGraphCodes.source_FP pairFst_mem_FP)
    (FlatAffineSlabGraphCodes.endpointWord_FP side)) (FlatAffineSlabGraphCodes.sampleWord_FP side)
theorem numericQuery_FP (side : Bool) : numericQuery side ∈ FP :=
  mem_FP_pair (mem_FP_pair FlatAffineSlabGraphCodes.source_FP (constFn_mem_FP []))
    (mem_FP_pair (FlatAffineSlabGraphCodes.sampleWord_FP side) FlatAffineSlabGraphCodes.gapWord_FP)

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {c | FlatAffineEndpointFiniteFrame.Valid F height (source c) ∧
    adjacentQuery false c ∈ FlatAffineEndpointAdjacentSamples.language F cone height true ∧
    adjacentQuery true c ∈ FlatAffineEndpointAdjacentSamples.language F cone height false ∧
    FlatAffineEndpointSampleSlab.numeric F cone height (numericQuery false c) ∧
    FlatAffineEndpointSampleSlab.numeric F cone height (numericQuery true c)}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have V := ((FlatAffineEndpointFiniteFrame.validDecider h cone height hh).precompose source FlatAffineSlabGraphCodes.source_FP).flagEvaluator
  have L := ((FlatAffineEndpointAdjacentSamples.decider h cone height hh true).precompose (adjacentQuery false) (adjacentQuery_FP false)).flagEvaluator
  have R := ((FlatAffineEndpointAdjacentSamples.decider h cone height hh false).precompose (adjacentQuery true) (adjacentQuery_FP true)).flagEvaluator
  have N := FlatAffineEndpointSampleSlab.numericDecider h cone height hh
  have NL := (N.precompose (numericQuery false) (numericQuery_FP false)).flagEvaluator
  have NR := (N.precompose (numericQuery true) (numericQuery_FP true)).flagEvaluator
  apply (V.andFlags (L.andFlags (R.andFlags (NL.andFlags NR)))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : language F cone height ∈ PSPACE :=
  (decider h cone height hh).mem_PSPACE

theorem adjacent_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    adjacentQuery side c ∈ FlatAffineEndpointAdjacentSamples.language F cone height (!side) := by
  cases side
  · exact hc.2.1
  · exact hc.2.2.1

def endpointRecord (side : Bool) (c : List Bool) : List Bool := IntegerPolynomialAdjacentSamples.endpointRecord (adjacentQuery side c)
def sampleRecord (side : Bool) (c : List Bool) : List Bool := IntegerPolynomialAdjacentSamples.sampleRecord (adjacentQuery side c)
theorem endpointRecord_packet (side : Bool) (c : List Bool) :
    endpointRecord side c = pair (pair (pairFst (source c)) (endpointWord side c)) [] := by
  simp only [endpointRecord, adjacentQuery, IntegerPolynomialAdjacentSamples.endpointRecord, pairFst_pair, pairSnd_pair]
theorem sampleRecord_packet (side : Bool) (c : List Bool) :
    sampleRecord side c = pair (pair (pairFst (source c)) (sampleWord side c)) [] := by
  simp only [sampleRecord, adjacentQuery, IntegerPolynomialAdjacentSamples.sampleRecord, pairFst_pair, pairSnd_pair]

theorem endpoint_record_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    endpointRecord side c ∈ IntegerPolynomialSampleSlice.valid (FlatAffineEndpointAdjacentSamples.heightSource F cone height) := by
  have H := adjacent_valid F cone height side c hc
  unfold FlatAffineEndpointAdjacentSamples.language at H
  exact H.2.1
theorem sample_record_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    sampleRecord side c ∈ IntegerPolynomialSampleSlice.valid (FlatAffineEndpointSamples.source F cone height) := by
  have H := adjacent_valid F cone height side c hc
  unfold FlatAffineEndpointAdjacentSamples.language at H
  exact H.2.2.1

theorem endpoint_label_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineEndpointAdjacentSamples.heightSource F cone height))
      (pairFst (source c)) (endpointWord side c) := by
  have H := endpoint_record_valid F cone height side c hc
  rw [endpointRecord_packet, IntegerPolynomialSampleSlice.valid_packet] at H
  exact H
theorem sample_label_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst (source c)) (sampleWord side c) := by
  have H := sample_record_valid F cone height side c hc
  rw [sampleRecord_packet, IntegerPolynomialSampleSlice.valid_packet] at H
  exact H

noncomputable def endpointValue (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) : ℝ :=
  IntegerPolynomialSampleSlice.point (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (endpointRecord side c)
noncomputable def sampleValue (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) : ℝ :=
  IntegerPolynomialSampleSlice.point (FlatAffineEndpointSamples.source F cone height) (sampleRecord side c)

theorem endpointValue_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    endpointValue F cone height side c = (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst (source c)) (endpointWord side c)
      (endpoint_label_valid F cone height side c hc)).val (0 : Fin 1) := by
  rw [endpointValue, endpointRecord_packet, IntegerPolynomialSampleSlice.point_packet _ _ _ [] (endpoint_label_valid F cone height side c hc)]
theorem sampleValue_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool) (hc : c ∈ language F cone height) :
    sampleValue F cone height side c = (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height)
      (pairFst (source c)) (sampleWord side c) (sample_label_valid F cone height side c hc)).val (0 : Fin 1) := by
  rw [sampleValue, sampleRecord_packet, IntegerPolynomialSampleSlice.point_packet _ _ _ [] (sample_label_valid F cone height side c hc)]
  rfl

end LeanCanny.Encoding.FlatAffineSlabGraphContext

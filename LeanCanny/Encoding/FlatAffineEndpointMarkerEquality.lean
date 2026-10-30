/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointMarkers

/-! # Native equality of endpoint point markers with arbitrary auxiliary copies -/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointMarkerEquality
open LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def left (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def right (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
def pointQuery (q : List Bool) : List Bool :=
  pair (pairFst (pairFst q)) (pair (pairFst (pairSnd q)) (pairSnd (pairSnd q)))
theorem left_FP : left ∈ FP := by polytime [left]
theorem right_FP : right ∈ FP := by polytime [right]
theorem pointQuery_FP : pointQuery ∈ FP := by polytime [pointQuery]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | left q ∈ FlatAffineEndpointMarkers.language F cone height ∧ right q ∈ FlatAffineEndpointMarkers.language F cone height ∧
    pointQuery q ∈ FlatAffineEndpointCopyEquality.language F cone height 1}

attribute [local irreducible] FlatAffineEndpointMarkers.language FlatAffineEndpointCopyEquality.language

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have D := FlatAffineEndpointMarkers.decider h cone height hh
  have L := (D.precompose left left_FP).flagEvaluator
  have R := (D.precompose right right_FP).flagEvaluator
  have E := ((FlatAffineEndpointCopyEquality.decider h cone height hh 1).precompose pointQuery pointQuery_FP).flagEvaluator
  apply (L.andFlags (R.andFlags E)).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s aWord w v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (hW : pair (pair s aWord) w ∈ FlatAffineEndpointMarkers.language F cone height)
    (hV : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height) :
    pair (pair s aWord) (pair w v) ∈ language F cone height ↔
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 1 =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1 := by
  have HW := (FlatAffineEndpointMarkers.packet F cone height s aWord w hs hw ha).mp hW
  have HV := (FlatAffineEndpointMarkers.packet F cone height s aWord v hs hv ha).mp hV
  have HH : FlatAffineEndpointCopyEquality.level F 1 s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      FlatAffineEndpointCopyEquality.level F 1 s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val := by
    simpa only [FlatAffineEndpointCopyEquality.level, show (1 : Fin 3) ≠ 0 by decide, ite_false] using HW.trans HV.symm
  simp only [language, Set.mem_ofPred_eq, left, right, pointQuery, pairFst_pair, pairSnd_pair, hW, hV, true_and]
  have P := FlatAffineEndpointCopyEquality.packet F cone height 1 s w v hs hw hv
  dsimp only at P
  exact P.trans (and_iff_right HH)

end LeanCanny.Encoding.FlatAffineEndpointMarkerEquality

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointCopyEquality
public import LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent

/-! # Native algebraic endpoint point markers for recursive slice queries

An independently encoded endpoint height is paired with a complete joint
label. Native identity checks bind the retained height to that scalar root.
The first endpoint copy is an actual point of the original endpoint fiber;
auxiliary copies need not be canonical.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointMarkers
open LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def endpointWord (q : List Bool) : List Bool := pairSnd (pairFst q)
def jointWord (q : List Bool) : List Bool := pairSnd q
def jointQuery (q : List Bool) : List Bool := pair (source q) (jointWord q)
def identityQuery (q : List Bool) : List Bool := pair (jointQuery q) (endpointWord q)
theorem jointQuery_FP : jointQuery ∈ FP := by polytime [jointQuery, source, jointWord]
theorem identityQuery_FP : identityQuery ∈ FP := by polytime [identityQuery, jointQuery, source, jointWord, endpointWord]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  {q | jointQuery q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    identityQuery q ∈ FlatAffineEndpointFiniteHeights.endpointLanguage F cone height}

attribute [local irreducible] GuardedSquareSampleInput.language FlatAffineEndpointFiniteHeights.endpointLanguage

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceDecider (language F cone height) := by
  have V := ((GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)).precompose jointQuery jointQuery_FP).flagEvaluator
  have E := ((FlatAffineEndpointFiniteHeights.endpointDecider h cone height hh).precompose identityQuery identityQuery_FP).flagEvaluator
  apply (V.andFlags E).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    language F cone height ∈ PSPACE := (decider h cone height hh).mem_PSPACE

theorem frame_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    FlatAffineEndpointFiniteFrame.Valid F height (source q) := by
  have H := hq.1
  unfold GuardedSquareSampleInput.language at H
  have HV := H.1
  change FlatAffineEndpointFiniteFrame.Valid F height (pairFst (jointQuery q)) at HV
  simpa only [jointQuery, pairFst_pair] using HV

theorem joint_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source q) (jointWord q) := by
  have H := hq.1
  unfold GuardedSquareSampleInput.language at H
  simpa only [FlatAffineEndpointFiniteSample.input, jointQuery, pairFst_pair, pairSnd_pair] using H.2

theorem endpoint_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineEndpointAdjacentSamples.heightSource F cone height))
      (pairFst (source q)) (endpointWord q) := by
  have H := hq.2
  unfold FlatAffineEndpointFiniteHeights.endpointLanguage SquareSampleScalarCoordinateEquality.language at H
  have HV := H.2.1
  simpa only [SquareSampleCompleteVertices.language, Set.mem_ofPred_eq, SquareSampleScalarCoordinateEquality.scalarVertex,
    SquareSampleScalarCoordinateEquality.source, identityQuery, jointQuery, pairFst_pair, pairSnd_pair] using HV

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s aWord w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord) :
    pair (pair s aWord) w ∈ language F cone height ↔
      FlatAffineEndpointFiniteProjection.endpoint F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1) := by
  have hg : pair s w ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s w) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, hw⟩
  simp only [language, Set.mem_ofPred_eq, jointQuery, identityQuery, source, endpointWord, jointWord,
    pairFst_pair, pairSnd_pair, hg, true_and]
  exact FlatAffineEndpointFiniteHeights.endpoint_packet F cone height s w aWord hs hw ha

theorem valid_length (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    (jointWord q).length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) :=
  (Classical.choose (joint_valid F cone height q hq)).1

theorem of_adjacent (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s w aWord tWord : List Bool)
    (hq : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height right) :
    pair (pair s aWord) w ∈ language F cone height := by
  constructor
  · simpa only [jointQuery, source, jointWord, pairFst_pair, pairSnd_pair] using hq.1
  · simpa only [identityQuery, jointQuery, source, jointWord, endpointWord,
      FlatAffineEndpointFiniteAdjacent.endpointQuery, pairFst_pair, pairSnd_pair] using hq.2.1

theorem point_in_fiber (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) (hq : q ∈ language F cone height) :
    let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
      (source q) (jointWord q) (joint_valid F cone height q hq)).val
    FlatAffineEndpointFiniteProjection.copy F (source q) z 1 ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source q)
      ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (FlatAffineEndpointAdjacentSamples.heightSource F cone height))
        (pairFst (source q)) (endpointWord q) (endpoint_valid F cone height q hq)).val (0 : Fin 1)) := by
  dsimp only
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F (source q)) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
      (source q) (jointWord q) (joint_valid F cone height q hq)).val
  have hs := frame_valid F cone height q hq
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) (source q) hs z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
      (source q) (jointWord q) (joint_valid F cone height q hq)).property
  have H := FlatAffineEndpointFiniteProjection.equations F height (source q) z hz
  have HE := (FlatAffineEndpointFiniteHeights.endpoint_packet F cone height (source q) (jointWord q) (endpointWord q) hs
    (joint_valid F cone height q hq) (endpoint_valid F cone height q hq)).mp hq.2
  intro i
  have Hi := H.2.2 (1 : Fin 3) i
  rw [HE] at Hi
  simpa using Hi

end LeanCanny.Encoding.FlatAffineEndpointMarkers

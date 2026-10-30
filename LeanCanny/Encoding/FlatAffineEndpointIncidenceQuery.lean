/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointMarkerEquality
public import LeanCanny.Encoding.FlatAffineEndpointBranchLabels
public import LeanCanny.Encoding.FlatAffineEndpointFiniteEdges

/-! # Native attachment queries for short branch and endpoint labels

A query stores `((frame, (endpoint, sample)), ((gap, descriptor), marker))`.
A bounded search finds a joint tuple whose current point has the requested
branch descriptor and whose endpoint copy denotes the marker point. Both
height identities, adjacency, original slab membership, and all-candidate
midpoint matching are checked by native polynomial-space computations.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointIncidenceQuery
open LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def source (q : List Bool) : List Bool := pairFst (pairFst q)
def endpointWord (q : List Bool) : List Bool := pairFst (pairSnd (pairFst q))
def sampleWord (q : List Bool) : List Bool := pairSnd (pairSnd (pairFst q))
def gapWord (q : List Bool) : List Bool := pairFst (pairFst (pairSnd q))
def descriptor (q : List Bool) : List Bool := pairSnd (pairFst (pairSnd q))
def markerWord (q : List Bool) : List Bool := pairSnd (pairSnd q)
def marker (q : List Bool) : List Bool := pair (pair (source q) (endpointWord q)) (markerWord q)
def branch (q : List Bool) : List Bool := pair (pair (source q) (pair (sampleWord q) (gapWord q))) (descriptor q)
def record (s a t g d v : List Bool) : List Bool := pair (pair s (pair a t)) (pair (pair g d) v)
theorem source_FP : source ∈ FP := by polytime [source]
def candidateQuery (r : List Bool) : List Bool := pair (source (pairFst r)) (pairSnd r)
def edgeQuery (r : List Bool) : List Bool :=
  pair (candidateQuery r) (pair (endpointWord (pairFst r)) (sampleWord (pairFst r)))
def slabQuery (r : List Bool) : List Bool :=
  pair (candidateQuery r) (pair (sampleWord (pairFst r)) (gapWord (pairFst r)))
def equalityQuery (r : List Bool) : List Bool :=
  pair (pair (source (pairFst r)) (endpointWord (pairFst r))) (pair (pairSnd r) (markerWord (pairFst r)))
def targetQuery (r : List Bool) : List Bool := descriptor (pairFst r)
theorem candidateQuery_FP : candidateQuery ∈ FP := by polytime [candidateQuery, source]
theorem edgeQuery_FP : edgeQuery ∈ FP := by polytime [edgeQuery, candidateQuery, source, endpointWord, sampleWord]
theorem slabQuery_FP : slabQuery ∈ FP := by polytime [slabQuery, candidateQuery, source, sampleWord, gapWord]
theorem equalityQuery_FP : equalityQuery ∈ FP := by polytime [equalityQuery, source, endpointWord, markerWord]
theorem targetQuery_FP : targetQuery ∈ FP := by polytime [targetQuery, descriptor]

noncomputable def accepts (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (r : List Bool) : Prop :=
  edgeQuery r ∈ FlatAffineEndpointFiniteEdges.language F cone height right ∧
    slabQuery r ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
    equalityQuery r ∈ FlatAffineEndpointMarkerEquality.language F cone height ∧
    FlatAffineEndpointRankWord.word F cone height (candidateQuery r) = targetQuery r

attribute [local irreducible] FlatAffineEndpointFiniteEdges.language FlatAffineEndpointSampleSlab.language
  FlatAffineEndpointMarkerEquality.language FlatAffineEndpointRankWord.word

theorem testEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    SpaceFunction (fun r => [decide (accepts F cone height right r)]) := by
  have A := ((FlatAffineEndpointFiniteEdges.decider h cone height hh right).precompose edgeQuery edgeQuery_FP).flagEvaluator
  have S := ((FlatAffineEndpointSampleSlab.decider h cone height hh).precompose slabQuery slabQuery_FP).flagEvaluator
  have P := ((FlatAffineEndpointMarkerEquality.decider h cone height hh).precompose equalityQuery equalityQuery_FP).flagEvaluator
  have W := (FlatAffineEndpointRankWord.evaluator h cone height hh).precompose candidateQuery candidateQuery_FP
  have T := SpaceFunction.ofFP targetQuery targetQuery_FP
  have E := (W.pairOutputs T).postcompose (fun z => [decide (pairFst z = pairSnd z)])
    (Brackets.stringEq_fppred pairFst_mem_FP pairSnd_mem_FP).flag_mem_FP
  exact (A.andFlags (S.andFlags (P.andFlags E))).congr (funext fun r => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [accepts, Set.mem_preimage, Function.comp_apply, pairFst_pair, pairSnd_pair,
      List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) : Language :=
  {q | ∃ w : List Bool, w.length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) ∧
    accepts F cone height right (pair q w)}

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    SpaceDecider (language F cone height right) := by
  have E := (testEvaluator h cone height hh right).exists_words
    ((FlatAffineEndpointFiniteSample.width_unary h cone height hh).comp source_FP)
  apply E.decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    language F cone height right ∈ PSPACE := (decider h cone height hh right).mem_PSPACE

theorem witness (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (q w : List Bool)
    (hq : accepts F cone height right (pair q w)) : q ∈ language F cone height right := by
  have hw := FlatAffineEndpointSampleSlab.joint_valid F cone height _ hq.2.1
  have H := (Classical.choose hw).1
  have hlen : w.length = SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height) (source q) := by
    simpa only [slabQuery, candidateQuery, pairFst_pair, pairSnd_pair, SquareSampleCompleteVertices.width] using H
  exact ⟨w, hlen, hq⟩

theorem marker_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (q : List Bool)
    (hq : q ∈ language F cone height right) : marker q ∈ FlatAffineEndpointMarkers.language F cone height := by
  obtain ⟨w, _, hw⟩ := hq
  have H := hw.2.2.1
  unfold FlatAffineEndpointMarkerEquality.language at H
  simpa only [FlatAffineEndpointMarkerEquality.right, equalityQuery, marker, pairFst_pair, pairSnd_pair] using H.2.1

theorem branch_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (q : List Bool)
    (hq : q ∈ language F cone height right) : branch q ∈ FlatAffineEndpointBranchLabels.language F cone height := by
  obtain ⟨w, _, hw⟩ := hq
  apply FlatAffineEndpointBranchLabels.witness F cone height (branch q) w
  · simpa only [FlatAffineEndpointBranchLabels.slabQuery, FlatAffineEndpointBranchLabels.candidateQuery,
      FlatAffineEndpointBranchLabels.source, FlatAffineEndpointBranchLabels.samplePacket,
      branch, slabQuery, candidateQuery, pairFst_pair, pairSnd_pair] using hw.2.1
  · simpa only [FlatAffineEndpointBranchLabels.candidateQuery, FlatAffineEndpointBranchLabels.source,
      FlatAffineEndpointBranchLabels.descriptor, branch, candidateQuery, targetQuery, pairFst_pair, pairSnd_pair] using hw.2.2.2

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s a t g d v w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) a)
    (hAdj : pair (pair s w) (pair a t) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height right)
    (hSlab : pair (pair s w) (pair t g) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s a) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (he : FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 1 =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1) :
    accepts F cone height right (pair (record s a t g d v) w) ↔
      pair (pair s w) (pair a t) ∈ FlatAffineEndpointFiniteEdges.language F cone height right ∧
        FlatAffineEndpointRankWord.word F cone height (pair s w) = d := by
  have hW := FlatAffineEndpointMarkers.of_adjacent F cone height right s w a t hAdj
  have hEq := (FlatAffineEndpointMarkerEquality.packet F cone height s a w v hs hw hv ha hW hMarker).mpr he
  simp only [accepts, edgeQuery, slabQuery, equalityQuery, candidateQuery, targetQuery, record,
    source, endpointWord, sampleWord, gapWord, descriptor, markerWord, pairFst_pair, pairSnd_pair,
    hSlab, hEq, true_and]

end LeanCanny.Encoding.FlatAffineEndpointIncidenceQuery

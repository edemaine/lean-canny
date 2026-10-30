/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteHeights

/-! # Native adjacent-sample validation tied to the joint root

A query contains the joint label and independently encoded endpoint and
sample labels. Native height comparisons bind both scalar values to the
joint tuple before the existing adjacency validator is applied.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def endpointQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def sampleQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd q))
def adjacentQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairFst (pairSnd q))) (pairSnd (pairSnd q))
theorem endpointQuery_FP : endpointQuery ∈ FP := by polytime [endpointQuery]
theorem sampleQuery_FP : sampleQuery ∈ FP := by polytime [sampleQuery]
theorem adjacentQuery_FP : adjacentQuery ∈ FP := by polytime [adjacentQuery]

noncomputable def language (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) : Language :=
  {q | pairFst q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) ∧
    endpointQuery q ∈ FlatAffineEndpointFiniteHeights.endpointLanguage F cone height ∧
    sampleQuery q ∈ FlatAffineEndpointFiniteHeights.sampleLanguage F cone height ∧
    adjacentQuery q ∈ FlatAffineEndpointAdjacentSamples.language F cone height right}

section native
attribute [local irreducible] FlatAffineEndpointFiniteSample.data FlatAffineEndpointFiniteSample.input
  FlatAffineEndpointFiniteHeights.endpointLanguage FlatAffineEndpointFiniteHeights.sampleLanguage
  FlatAffineEndpointAdjacentSamples.language GuardedSquareSampleInput.language

theorem decider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    SpaceDecider (language F cone height right) := by
  have V := ((GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)).precompose
    pairFst pairFst_mem_FP).flagEvaluator
  have E := ((FlatAffineEndpointFiniteHeights.endpointDecider h cone height hh).precompose endpointQuery endpointQuery_FP).flagEvaluator
  have T := ((FlatAffineEndpointFiniteHeights.sampleDecider h cone height hh).precompose sampleQuery sampleQuery_FP).flagEvaluator
  have A := ((FlatAffineEndpointAdjacentSamples.decider h cone height hh right).precompose adjacentQuery adjacentQuery_FP).flagEvaluator
  apply (V.andFlags (E.andFlags (T.andFlags A))).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq]

theorem mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) (right : Bool) :
    language F cone height right ∈ PSPACE := (decider h cone height hh right).mem_PSPACE

end native

attribute [local irreducible] FlatAffineEndpointFiniteHeights.endpointLanguage FlatAffineEndpointFiniteHeights.sampleLanguage
  FlatAffineEndpointAdjacentSamples.language GuardedSquareSampleInput.language

theorem packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s w aWord tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord) :
    pair (pair s w) (pair aWord tWord) ∈ language F cone height right ↔
      FlatAffineEndpointFiniteProjection.endpoint F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
        (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
          (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1) ∧
      FlatAffineEndpointFiniteProjection.sample F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord ht).val (0 : Fin 1) ∧
      pair (pair (pairFst s) aWord) tWord ∈ FlatAffineEndpointAdjacentSamples.language F cone height right := by
  have hg : pair s w ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s w) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, hw⟩
  simp only [language, Set.mem_ofPred_eq, endpointQuery, sampleQuery, adjacentQuery, pairFst_pair, pairSnd_pair, hg, true_and]
  rw [FlatAffineEndpointFiniteHeights.endpoint_packet F cone height s w aWord hs hw ha,
    FlatAffineEndpointFiniteHeights.sample_packet F cone height s w tWord hs hw ht]

theorem gap (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s w aWord tWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card)
    (hi : OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i =
      FlatAffineEndpointFiniteProjection.endpoint F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val)
    (hq : pair (pair s w) (pair aWord tWord) ∈ language F cone height right) :
    FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val ∈
      OrderedRealCells.gap (FlatAffineEndpointCells.roots F cone height (pairFst s))
        (if right then OrderedRealCells.rightGap _ i else OrderedRealCells.leftGap _ i) := by
  have HP := (packet F cone height right s w aWord tWord hs hw ha ht).mp hq
  let aq := pair (pair (pairFst s) aWord) tWord
  have he : IntegerPolynomialAdjacentSamples.endpointRecord aq ∈
      IntegerPolynomialSampleSlice.valid (FlatAffineEndpointAdjacentSamples.heightSource F cone height) := by
    simp only [aq, IntegerPolynomialAdjacentSamples.endpointRecord, pairFst_pair, pairSnd_pair]
    exact (IntegerPolynomialSampleSlice.valid_packet _ _ _ [] ).mpr ha
  have ht' : IntegerPolynomialAdjacentSamples.sampleRecord aq ∈
      IntegerPolynomialSampleSlice.valid (FlatAffineEndpointSamples.source F cone height) := by
    simp only [aq, IntegerPolynomialAdjacentSamples.sampleRecord, pairFst_pair, pairSnd_pair]
    exact (IntegerPolynomialSampleSlice.valid_packet _ _ _ [] ).mpr ht
  have hadj := HP.2.2
  unfold FlatAffineEndpointAdjacentSamples.language at hadj
  have H := (IntegerPolynomialAdjacentSamples.language_iff
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (FlatAffineEndpointSamples.source F cone height)
    (FlatAffineEndpointCells.source F cone height) right aq he ht').mp hadj.2
  simp only [aq, IntegerPolynomialAdjacentSamples.endpointRecord, IntegerPolynomialAdjacentSamples.sampleRecord,
    pairFst_pair, pairSnd_pair, IntegerPolynomialSampleSlice.point_packet _ _ _ [] ha,
    IntegerPolynomialSampleSlice.point_packet _ _ _ [] ht] at H
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  let a := FlatAffineEndpointFiniteProjection.endpoint F s z
  let t := FlatAffineEndpointFiniteProjection.sample F s z
  have hA : a = (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1) := HP.1
  have hT : t = (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointSamples.source F cone height)) (pairFst s) tWord ht).val (0 : Fin 1) := HP.2.1
  rw [← hA, ← hT] at H
  have hi' : OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i = a := hi
  rw [← hi'] at H
  change t ∈ OrderedRealCells.gap (FlatAffineEndpointCells.roots F cone height (pairFst s))
    (if right then OrderedRealCells.rightGap _ i else OrderedRealCells.leftGap _ i)
  cases right
  · apply (OrderedRealCells.mem_leftGap_iff_rank _ i _).mpr
    exact ⟨H.2.1, by simpa only [FlatAffineEndpointCells.roots, Bool.false_eq_true, ite_false, Nat.add_zero] using H.2.2⟩
  · exact (OrderedRealCells.mem_rightGap_iff_rank _ i _).mpr H.2

end LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent

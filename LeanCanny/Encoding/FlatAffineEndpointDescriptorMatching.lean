/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointIncidenceQuery
public import LeanCanny.Encoding.FlatAffineEndpointRankWordSample

/-! # Sound attachment queries at a fixed short branch descriptor

An accepted bounded query matches the stated endpoint marker to the actual
reference branch point. Its existential auxiliary tuple cannot change that
point: the checked scalar sample and the native rank descriptor identify it.
The finite geometric fiber is used only in this correctness theorem.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointDescriptorMatching
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointRankWord
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

attribute [local irreducible] FlatAffineEndpointRankWord.word FlatAffineEndpointFiniteEdges.language
  FlatAffineEndpointMarkerEquality.language FlatAffineEndpointSampleSlab.language

private theorem slab_of_equal_sample (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s r w tWord gapWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hr : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s r)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (he : FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val =
      FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val)
    (hSlab : pair (pair s r) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height) :
    pair (pair s w) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height := by
  have ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord := by
    simpa only [FlatAffineEndpointSampleSlab.sampleWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointSampleSlab.sample_valid F cone height _ hSlab
  unfold FlatAffineEndpointSampleSlab.language at hSlab ⊢
  have HI := (FlatAffineEndpointFiniteHeights.sample_packet F cone height s r tWord hs hr ht).mp (by
    simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
      pairFst_pair, pairSnd_pair] using hSlab.2.1)
  refine ⟨?_, ?_, ?_⟩
  · simp only [pairFst_pair]
    unfold GuardedSquareSampleInput.language
    change pairFst (pair s w) ∈ (FlatAffineEndpointFiniteSample.data F cone height).good ∧
      SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst (pair s w)) (pairSnd (pair s w))
    rw [pairFst_pair, pairSnd_pair]
    exact ⟨hs, hw⟩
  · simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
      pairFst_pair, pairSnd_pair] using
      (FlatAffineEndpointFiniteHeights.sample_packet F cone height s w tWord hs hw ht).mpr (he.symm.trans HI)
  · simpa only [FlatAffineEndpointSampleSlab.numeric, FlatAffineEndpointSampleSlab.record,
      FlatAffineEndpointSampleSlab.sampleWord, FlatAffineEndpointSampleSlab.gapWord,
      pairFst_pair, pairSnd_pair] using hSlab.2.2

theorem sound {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s r v aWord tWord gapWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hr : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s r)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (hView : BranchView F cone height points j s r)
    (hSlab : pair (pair s r) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (right : Bool)
    (hq : FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
      FlatAffineEndpointIncidenceQuery.language F cone height right) :
    EndpointMidpoint.Matches
      (FlatAffineEndpointFiniteMatching.endpointFiber F height s
        ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
          (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1)))
      (FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1)
      (FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val 0) := by
  obtain ⟨w, _, hwitness⟩ := hq
  have H : pair (pair s w) (pair aWord tWord) ∈ FlatAffineEndpointFiniteEdges.language F cone height right ∧
      pair (pair s w) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height ∧
      pair (pair s aWord) (pair w v) ∈ FlatAffineEndpointMarkerEquality.language F cone height ∧
      word F cone height (pair s w) = word F cone height (pair s r) := by
    simpa only [FlatAffineEndpointIncidenceQuery.accepts, FlatAffineEndpointIncidenceQuery.record,
      FlatAffineEndpointIncidenceQuery.edgeQuery, FlatAffineEndpointIncidenceQuery.slabQuery,
      FlatAffineEndpointIncidenceQuery.equalityQuery, FlatAffineEndpointIncidenceQuery.candidateQuery,
      FlatAffineEndpointIncidenceQuery.targetQuery, FlatAffineEndpointIncidenceQuery.source,
      FlatAffineEndpointIncidenceQuery.endpointWord, FlatAffineEndpointIncidenceQuery.sampleWord,
      FlatAffineEndpointIncidenceQuery.gapWord, FlatAffineEndpointIncidenceQuery.descriptor,
      FlatAffineEndpointIncidenceQuery.markerWord, pairFst_pair, pairSnd_pair] using hwitness
  have hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w := by
    simpa only [pairFst_pair, pairSnd_pair] using FlatAffineEndpointSampleSlab.joint_valid F cone height _ H.2.1
  have ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord := by
    simpa only [FlatAffineEndpointSampleSlab.sampleWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointSampleSlab.sample_valid F cone height _ hSlab
  have SW := H.2.1
  have SR := hSlab
  unfold FlatAffineEndpointSampleSlab.language at SW SR
  have hSw := (FlatAffineEndpointFiniteHeights.sample_packet F cone height s w tWord hs hw ht).mp (by
    simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
      pairFst_pair, pairSnd_pair] using SW.2.1)
  have hSr := (FlatAffineEndpointFiniteHeights.sample_packet F cone height s r tWord hs hr ht).mp (by
    simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
      pairFst_pair, pairSnd_pair] using SR.2.1)
  have TW : sampleValue F cone height s w = FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val :=
    congrArg (FlatAffineEndpointFiniteProjection.sample F s) (anchorPoint_packet F cone height s w hw)
  have TR : sampleValue F cone height s r = FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val :=
    congrArg (FlatAffineEndpointFiniteProjection.sample F s) (anchorPoint_packet F cone height s r hr)
  have hT : sampleValue F cone height s w = sampleValue F cone height s r := TW.trans ((hSw.trans hSr.symm).trans TR.symm)
  have hRoot : currentValue F cone height s w ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s
      (sampleValue F cone height s r) := by
    rw [← hT]
    exact current_in_fiber F cone height s w hs hw
  obtain ⟨k, hk⟩ := hView.2.1 _ hRoot
  have hW := view_at_sample F cone height points k s w (sampleValue F cone height s r)
    hView.1 hView.2.1 hT hk.symm
  have C := word_eq_implies_current_eq F cone height points k j s w r hs hw hr hW hView hT H.2.2.2
  have CW : currentValue F cone height s w = FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 0 :=
    congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) (anchorPoint_packet F cone height s w hw)
  have CR : currentValue F cone height s r = FlatAffineEndpointFiniteProjection.copy F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val 0 :=
    congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) (anchorPoint_packet F cone height s r hr)
  have hCurrent := CW.symm.trans (C.trans CR)
  have EQ := H.2.2.1
  unfold FlatAffineEndpointMarkerEquality.language at EQ
  have hMarkerW : pair (pair s aWord) w ∈ FlatAffineEndpointMarkers.language F cone height := by
    simpa only [FlatAffineEndpointMarkerEquality.left, pairFst_pair, pairSnd_pair] using EQ.1
  have hPoint := (FlatAffineEndpointMarkerEquality.packet F cone height s aWord w v hs hw hv ha hMarkerW hMarker).mp H.2.2.1
  have hA := (FlatAffineEndpointMarkers.packet F cone height s aWord w hs hw ha).mp hMarkerW
  have E := H.1
  unfold FlatAffineEndpointFiniteEdges.language at E
  have M := FlatAffineEndpointFiniteMatching.packet F cone height s w hs hw
  dsimp only at M
  have HM := M.mp (by simpa only [pairFst_pair] using E.2)
  simpa only [hA, hPoint, hCurrent] using HM

theorem complete {J : Type*} [Fintype J] [LinearOrder J]
    (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u))
    (points : (s : List Bool) → ℝ → J → Fin (FlatAffineEndpointFiniteSide.originalCount F s) → ℝ)
    (j : J) (s r v aWord tWord gapWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hr : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s r)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (hView : BranchView F cone height points j s r)
    (hSlab : pair (pair s r) (pair tWord gapWord) ∈ FlatAffineEndpointSampleSlab.language F cone height)
    (hMarker : pair (pair s aWord) v ∈ FlatAffineEndpointMarkers.language F cone height)
    (right : Bool)
    (hAdj : pair (pair s r) (pair aWord tWord) ∈ FlatAffineEndpointFiniteAdjacent.language F cone height right)
    (hMatch : EndpointMidpoint.Matches
      (FlatAffineEndpointFiniteMatching.endpointFiber F height s
        ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
          (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1)))
      (FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val 1)
      (FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val 0)) :
    FlatAffineEndpointIncidenceQuery.record s aWord tWord gapWord (word F cone height (pair s r)) v ∈
      FlatAffineEndpointIncidenceQuery.language F cone height right := by
  let zr : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).val
  let zv : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).val
  let a : ℝ := (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1)
  let t := FlatAffineEndpointFiniteProjection.sample F s zr
  let cur := FlatAffineEndpointFiniteProjection.copy F s zr 0
  let x := FlatAffineEndpointFiniteProjection.copy F s zv 1
  have rootsR := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs zr).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s r hr).property
  have rootsV := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs zv).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s v hv).property
  have PR := FlatAffineEndpointFiniteProjection.equations F height s zr rootsR
  have PV := FlatAffineEndpointFiniteProjection.equations F height s zv rootsV
  have hVA : FlatAffineEndpointFiniteProjection.endpoint F s zv = a :=
    (FlatAffineEndpointMarkers.packet F cone height s aWord v hs hv ha).mp hMarker
  have haRoot : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0 := by
    have H := PV.2.1
    rw [hVA] at H
    exact H
  have hx : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s a := by
    intro i
    have H := PV.2.2 (1 : Fin 3) i
    rw [hVA] at H
    simpa only [x, show (1 : Fin 3) ≠ 0 by decide, ite_false] using H
  obtain ⟨w, hw, _, he⟩ := FlatAffineEndpointFiniteSample.tuple_label_exists F cone height s hs a t cur x x
    haRoot PR.1 (by intro i; simpa only [cur, t, ite_true] using PR.2.2 (0 : Fin 3) i) hx hx
  have AW := (congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
    (FlatAffineEndpointFiniteProjection.endpoint_point F s a t cur x x)
  have TW := (congrArg (FlatAffineEndpointFiniteProjection.sample F s) he).trans
    (FlatAffineEndpointFiniteProjection.sample_point F s a t cur x x)
  have CW := (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) he).trans
    (FlatAffineEndpointFiniteProjection.copy_point F s a t cur x x 0)
  have XW := (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1) he).trans
    (FlatAffineEndpointFiniteProjection.copy_point F s a t cur x x 1)
  have ht : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) tWord := by
    simpa only [FlatAffineEndpointSampleSlab.sampleWord, pairFst_pair, pairSnd_pair] using
      FlatAffineEndpointSampleSlab.sample_valid F cone height _ hSlab
  have AP := (FlatAffineEndpointFiniteAdjacent.packet F cone height right s r aWord tWord hs hr ha ht).mp hAdj
  have hAdjW := (FlatAffineEndpointFiniteAdjacent.packet F cone height right s w aWord tWord hs hw ha ht).mpr
    ⟨AW, TW.trans AP.2.1, AP.2.2⟩
  have hSlabW := slab_of_equal_sample F cone height s r w tWord gapWord hs hr hw TW.symm hSlab
  have wrapTW := congrArg (FlatAffineEndpointFiniteProjection.sample F s) (anchorPoint_packet F cone height s w hw)
  have wrapTR := congrArg (FlatAffineEndpointFiniteProjection.sample F s) (anchorPoint_packet F cone height s r hr)
  have sameT : sampleValue F cone height s w = sampleValue F cone height s r := wrapTW.trans (TW.trans wrapTR.symm)
  have wrapCW := congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) (anchorPoint_packet F cone height s w hw)
  have wrapCR := congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) (anchorPoint_packet F cone height s r hr)
  have sameC : currentValue F cone height s w = currentValue F cone height s r := wrapCW.trans (CW.trans wrapCR.symm)
  have viewW := view_at_sample F cone height points j s w (sampleValue F cone height s r)
    hView.1 hView.2.1 sameT (sameC.trans hView.2.2)
  have sameWord := word_eq_of_same_sample_branch F cone height points j s w r hs hw hr viewW hView sameT
  have hm := (FlatAffineEndpointFiniteMatching.tuple_packet F cone height s w hs hw a t cur x x he).mpr hMatch
  have hEdge := (FlatAffineEndpointFiniteEdges.packet F cone height right s w aWord tWord hAdjW).mpr hm
  apply FlatAffineEndpointIncidenceQuery.witness F cone height right _ w
  exact (FlatAffineEndpointIncidenceQuery.packet F cone height right s aWord tWord gapWord _ v w hs hw hv ha
    hAdjW hSlabW hMarker XW).mpr ⟨hEdge, sameWord⟩

end LeanCanny.Encoding.FlatAffineEndpointDescriptorMatching

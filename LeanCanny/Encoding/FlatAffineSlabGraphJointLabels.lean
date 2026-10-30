/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineSlabGraphContextInterval
public import LeanCanny.Encoding.FlatAffineEndpointFiniteComplete
public import LeanCanny.Encoding.FlatAffineEndpointRankWordSample

/-! # Native joint labels at every point of a checked slab sample

The scalar context and actual spatial roots construct a complete joint label.
Its native sample, endpoint, and adjacency checks all hold. No spatial label
oracle or nonsingularity assumption is required.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlabGraphContext
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineSlabGraphCodes (source gapWord endpointWord sampleWord)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem sample_root (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool)
    (hc : c ∈ language F cone height) :
    SymbolicScaledSquarefree.scalarEvaluation (sampleValue F cone height side c)
      (FlatAffineEndpointFiniteFrame.retained F height (pairFst (source c))) = 0 := by
  have HN := FlatAffineEndpointSamples.source_ne_zero F cone height (pairFst (source c)) hc.1.1
    (endpointValue F cone height side c) (endpoint_root F cone height side c hc)
  have HR := (IntegerPolynomialSampleInput.roots_iff (FlatAffineEndpointSamples.source F cone height)
    (pairFst (source c)) HN _).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height)
      (pairFst (source c)) (sampleWord side c) (sample_label_valid F cone height side c hc)).property
  rw [← sampleValue_packet F cone height side c hc] at HR
  exact HR

theorem joint_label_exists (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (side : Bool) (c : List Bool)
    (hc : c ∈ language F cone height)
    (x y : Fin (count F (pairFst (pairFst (source c)))) → ℝ)
    (hx : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source c) (sampleValue F cone height side c))
    (hy : y ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (source c) (endpointValue F cone height side c)) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (source c) w,
      FlatAffineEndpointRankWord.sampleValue F cone height (source c) w = sampleValue F cone height side c ∧
      FlatAffineEndpointRankWord.currentValue F cone height (source c) w = x ∧
      FlatAffineEndpointFiniteProjection.copy F (source c)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) (source c) w hw).val 1 = y ∧
      pair (pair (source c) w) (pair (endpointWord side c) (sampleWord side c)) ∈
        FlatAffineEndpointFiniteAdjacent.language F cone height (!side) ∧
      pair (pair (source c) w) (pair (sampleWord side c) (gapWord c)) ∈
        FlatAffineEndpointSampleSlab.language F cone height := by
  let s := source c
  let a := endpointValue F cone height side c
  let t := sampleValue F cone height side c
  obtain ⟨w, hw, hg, he⟩ := FlatAffineEndpointFiniteSample.tuple_label_exists F cone height s hc.1 a t x y y
    (endpoint_root F cone height side c hc) (sample_root F cone height side c hc) hx hy hy
  have HA := (congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
    (FlatAffineEndpointFiniteProjection.endpoint_point F s a t x y y)
  have HT := (congrArg (FlatAffineEndpointFiniteProjection.sample F s) he).trans
    (FlatAffineEndpointFiniteProjection.sample_point F s a t x y y)
  have HC := (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0) he).trans
    (FlatAffineEndpointFiniteProjection.copy_point F s a t x y y 0)
  have HY := (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1) he).trans
    (FlatAffineEndpointFiniteProjection.copy_point F s a t x y y 1)
  refine ⟨w, hw, ?_, ?_, HY, ?_, ?_⟩
  · exact (congrArg (FlatAffineEndpointFiniteProjection.sample F s)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s w hw)).trans HT
  · exact (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0)
      (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s w hw)).trans HC
  · apply (FlatAffineEndpointFiniteAdjacent.packet F cone height (!side) s w (endpointWord side c) (sampleWord side c)
      hc.1 hw (endpoint_label_valid F cone height side c hc) (sample_label_valid F cone height side c hc)).mpr
    exact ⟨HA.trans (endpointValue_packet F cone height side c hc),
      HT.trans (sampleValue_packet F cone height side c hc), adjacent_valid F cone height side c hc⟩
  · constructor
    · simpa only [pairFst_pair] using hg
    · constructor
      · have H := (FlatAffineEndpointFiniteHeights.sample_packet F cone height s w (sampleWord side c)
          hc.1 hw (sample_label_valid F cone height side c hc)).mpr
          (HT.trans (sampleValue_packet F cone height side c hc))
        simpa only [FlatAffineEndpointSampleSlab.identityQuery, FlatAffineEndpointSampleSlab.sampleWord,
          pairFst_pair, pairSnd_pair] using H
      · have H : FlatAffineEndpointSampleSlab.numeric F cone height (numericQuery side c) := by
          cases side
          · exact hc.2.2.2.1
          · exact hc.2.2.2.2
        simpa only [FlatAffineEndpointSampleSlab.numeric, FlatAffineEndpointSampleSlab.record,
          FlatAffineEndpointSampleSlab.sampleWord, FlatAffineEndpointSampleSlab.gapWord,
          numericQuery, pairFst_pair, pairSnd_pair, s] using H

end LeanCanny.Encoding.FlatAffineSlabGraphContext

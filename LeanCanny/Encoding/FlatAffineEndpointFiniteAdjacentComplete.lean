/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent
public import LeanCanny.Encoding.IntegerPolynomialAdjacentSamplesComplete

/-! # Completeness of the joint adjacent-height validator

Every valid joint tuple in the required gap has independent complete scalar
labels that the native height and adjacency validators accept together.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem labels_exist (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (right : Bool) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (i : Fin (FlatAffineEndpointCells.roots F cone height (pairFst s)).card)
    (hi : OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i =
      FlatAffineEndpointFiniteProjection.endpoint F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val)
    (hgap : FlatAffineEndpointFiniteProjection.sample F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val ∈
      OrderedRealCells.gap (FlatAffineEndpointCells.roots F cone height (pairFst s))
        (if right then OrderedRealCells.rightGap _ i else OrderedRealCells.leftGap _ i)) :
    ∃ aWord tWord, pair (pair s w) (pair aWord tWord) ∈ language F cone height right := by
  let z : Fin (FlatAffineEndpointFiniteFrame.arity F s) → ℝ :=
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  let S := FlatAffineEndpointAdjacentSamples.heightSource F cone height
  let T := FlatAffineEndpointSamples.source F cone height
  let Q := FlatAffineEndpointCells.source F cone height
  obtain ⟨aWord, ha, hea⟩ := IntegerPolynomialSampleInput.root_complete S (pairFst s)
    (FlatAffineHeightSlabExceptional.ne_zero F cone height _) (FlatAffineEndpointFiniteProjection.endpoint F s z) H.2.1
  have hiWord : OrderedRealCells.root (FlatAffineEndpointCells.roots F cone height (pairFst s)) i =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S) (pairFst s) aWord ha).val (0 : Fin 1) :=
    hi.trans hea.symm
  obtain ⟨tWord, ht, het, hadj⟩ := IntegerPolynomialAdjacentSamples.sample_label_complete_point S T Q right
    (pairFst s) aWord ha i hiWord (FlatAffineEndpointFiniteProjection.sample F s z)
    (FlatAffineEndpointSamples.derivative_ne_zero F cone height (pairFst s) hs.1 _ H.2.1) H.1 hgap
  refine ⟨aWord, tWord, (packet F cone height right s w aWord tWord hs hw ha ht).mpr ⟨hea.symm, het.symm, ?_⟩⟩
  change FlatAffineEndpointValidity.Valid F height (pairFst (pairFst (pair (pair (pairFst s) aWord) tWord))) ∧ _
  refine ⟨?_, hadj⟩
  simpa only [pairFst_pair] using hs.1

end LeanCanny.Encoding.FlatAffineEndpointFiniteAdjacent

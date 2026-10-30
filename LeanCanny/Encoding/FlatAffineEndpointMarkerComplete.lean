/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointMarkers
public import LeanCanny.Encoding.FlatAffineEndpointFiniteComplete

/-! # Every actual endpoint point has a native marker

The retained scalar source contains the exceptional heights themselves.
Taking the current height equal to the endpoint height and all three copies
equal to the endpoint point gives a valid joint tuple. This includes isolated
points with no spatial roots in either neighboring open slab.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointMarkers
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem complete (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s aWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (x : Fin (count F (pairFst (pairFst s))) → ℝ)
    (hx : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s
      ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1))) :
    ∃ w, ∃ hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w,
      pair (pair s aWord) w ∈ language F cone height ∧
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val 1 = x := by
  let a : ℝ := (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1)
  have hRoot : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst (pairFst s))) = 0 :=
    (IntegerPolynomialSampleInput.roots_iff (FlatAffineEndpointAdjacentSamples.heightSource F cone height) (pairFst s)
      (FlatAffineHeightSlabExceptional.ne_zero F cone height (pairFst (pairFst s))) _).mp
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).property
  have hSample : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineEndpointFiniteFrame.retained F height (pairFst s)) = 0 :=
    FlatAffineEndpointSamples.retains_endpoint F cone height (pairFst s) a hRoot
  obtain ⟨w, hw, _, he⟩ := FlatAffineEndpointFiniteSample.tuple_label_exists F cone height s hs a a x x x
    hRoot hSample hx hx hx
  have HE : FlatAffineEndpointFiniteProjection.endpoint F s
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val = a :=
    (congrArg (FlatAffineEndpointFiniteProjection.endpoint F s) he).trans
      (FlatAffineEndpointFiniteProjection.endpoint_point F s a a x x x)
  exact ⟨w, hw, (packet F cone height s aWord w hs hw ha).mpr HE,
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1) he).trans
      (FlatAffineEndpointFiniteProjection.copy_point F s a a x x x 1)⟩

theorem endpoint_record_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool)
    (hr : FlatAffineEndpointValidity.Valid F height r) (a : ℝ)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a
      (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0) :
    FlatAffineEndpointFiniteFrame.Valid F height (FlatAffineEndpointFiniteFrame.record F height r) :=
  FlatAffineEndpointFiniteSample.record_valid F cone height r hr a a ha
    (FlatAffineEndpointSamples.retains_endpoint F cone height r a ha)

end LeanCanny.Encoding.FlatAffineEndpointMarkers

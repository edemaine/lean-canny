/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointMarkers
public import LeanCanny.Encoding.SquareSampleCompleteParameterSlice

/-! # Native scalar records recovering actual algebraic endpoint markers

The scalar parameter is computed from the original joint point label. Its
rational coordinate recovery preserves the designated endpoint point and
the original endpoint fiber. No regularity is assumed at the endpoint.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointAlgebraicMarker
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable def source (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : IntegerPolynomialRootQueriesBits.Source :=
  SquareSampleCompleteParameterTest.source (FlatAffineEndpointFiniteSample.input F cone height)

theorem sourceAccess {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    IntegerPolynomialRootQueriesBits.Access (source F cone height) :=
  SquareSampleCompleteParameterTest.sourceAccess (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)

noncomputable def record (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : List Bool → List Bool :=
  SquareSampleCompleteParameterChoice.record (FlatAffineEndpointFiniteSample.input F cone height) ∘ FlatAffineEndpointMarkers.jointQuery

theorem recordEvaluator {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) : SpaceFunction (record F cone height) :=
  (SquareSampleCompleteParameterChoice.recordEvaluator (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)).precompose
    FlatAffineEndpointMarkers.jointQuery FlatAffineEndpointMarkers.jointQuery_FP

theorem record_valid (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height) :
    record F cone height q ∈ IntegerPolynomialSampleSlice.valid (source F cone height) :=
  SquareSampleCompleteParameterChoice.record_valid (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q)
    (FlatAffineEndpointMarkers.joint_valid F cone height q hq)

noncomputable def recovered (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) :
    Fin (count F (pairFst (pairFst (FlatAffineEndpointMarkers.source q)))) → ℝ :=
  FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointMarkers.source q)
    (SquareSampleParameters.decode (FlatAffineEndpointFiniteSample.input F cone height) (FlatAffineEndpointMarkers.source q)
      (IntegerPolynomialSampleSlice.point (source F cone height) (record F cone height q))) 1

theorem recovered_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height) :
    recovered F cone height q = FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointMarkers.source q)
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
        (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q)
        (FlatAffineEndpointMarkers.joint_valid F cone height q hq)).val 1 := by
  have H := SquareSampleCompleteParameterChoice.decode_record (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q)
    (FlatAffineEndpointMarkers.joint_valid F cone height q hq)
  exact congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointMarkers.source q) z 1) H

theorem recovered_in_fiber (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height) :
    recovered F cone height q ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height (FlatAffineEndpointMarkers.source q)
      ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input (FlatAffineEndpointAdjacentSamples.heightSource F cone height))
        (pairFst (FlatAffineEndpointMarkers.source q)) (FlatAffineEndpointMarkers.endpointWord q)
        (FlatAffineEndpointMarkers.endpoint_valid F cone height q hq)).val (0 : Fin 1)) := by
  rw [recovered_packet F cone height q hq]
  exact FlatAffineEndpointMarkers.point_in_fiber F cone height q hq

end LeanCanny.Encoding.FlatAffineEndpointAlgebraicMarker

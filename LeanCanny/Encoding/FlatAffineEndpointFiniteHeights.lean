/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleScalarCoordinateEquality
public import LeanCanny.Encoding.FlatAffineEndpointFiniteMatching

/-! # Joint heights identified with independently encoded endpoint samples

Original endpoint and derivative sources retain their original complete
scalar labels. Native derivative probes compare those roots with either
retained joint coordinate, including repeated roots of both sources.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointFiniteHeights
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def endpointIndex (F : Inputs) (s : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F s) :=
  FrozenAffineCopies.block (0 : Fin 1) (FlatAffineEndpointRows.zero F (pairFst s))
def sampleIndex (F : Inputs) (s : List Bool) : Fin (FlatAffineEndpointFiniteFrame.arity F s) := ⟨0, Nat.zero_lt_succ _⟩

theorem endpointIndex_unary (F : Inputs) : UnaryFn (fun s => (endpointIndex F s).val) :=
  (UnaryFn.const 1).of_eq (fun s => by
    change 1 = 0 + FlatAffineEndpointRows.arity F (pairFst s) * 0 + 1
    omega)
theorem sampleIndex_unary (F : Inputs) : UnaryFn (fun s => (sampleIndex F s).val) := UnaryFn.const 0

noncomputable def endpointLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  SquareSampleScalarCoordinateEquality.language (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height) pairFst (endpointIndex F)

noncomputable def sampleLanguage (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : Language :=
  SquareSampleScalarCoordinateEquality.language (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointSamples.source F cone height) pairFst (sampleIndex F)

theorem endpointDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (endpointLanguage F cone height) :=
  SquareSampleScalarCoordinateEquality.decider (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
    (FlatAffineEndpointAdjacentSamples.heightAccess h cone height hh) pairFst_mem_FP (endpointIndex F) (endpointIndex_unary F)

theorem sampleDecider {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    SpaceDecider (sampleLanguage F cone height) :=
  SquareSampleScalarCoordinateEquality.decider (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)
    (FlatAffineEndpointSamples.access h cone height hh) pairFst_mem_FP (sampleIndex F) (sampleIndex_unary F)

theorem endpoint_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    endpointLanguage F cone height ∈ PSPACE := (endpointDecider h cone height hh).mem_PSPACE

theorem sample_mem_PSPACE {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    sampleLanguage F cone height ∈ PSPACE := (sampleDecider h cone height hh).mem_PSPACE

attribute [local irreducible] SquareSampleScalarCoordinateEquality.language

theorem endpoint_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) v) :
    pair (pair s w) v ∈ endpointLanguage F cone height ↔
      FlatAffineEndpointFiniteProjection.endpoint F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) v hv).val (0 : Fin 1) := by
  let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  exact SquareSampleScalarCoordinateEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointAdjacentSamples.heightSource F cone height) pairFst (endpointIndex F) s w v hw hv
    (FlatAffineHeightSlabExceptional.ne_zero F cone height _) H.2.1

theorem sample_packet (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w v : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (hv : SquareSampleCompleteVertices.Valid (FlatAffineEndpointSamples.input F cone height) (pairFst s) v) :
    pair (pair s w) v ∈ sampleLanguage F cone height ↔
      FlatAffineEndpointFiniteProjection.sample F s
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val =
      (SquareSampleCompleteVertices.candidate (FlatAffineEndpointSamples.input F cone height) (pairFst s) v hv).val (0 : Fin 1) := by
  let z := (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).val
  have hz := (GuardedSquareSampleInput.roots_iff (FlatAffineEndpointFiniteSample.data F cone height) s hs z).mp
    (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height) s w hw).property
  have H := FlatAffineEndpointFiniteProjection.equations F height s z hz
  exact SquareSampleScalarCoordinateEquality.packet (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointSamples.source F cone height) pairFst (sampleIndex F) s w v hw hv
    (FlatAffineEndpointSamples.source_ne_zero F cone height (pairFst s) hs.1 _ H.2.1) H.1

end LeanCanny.Encoding.FlatAffineEndpointFiniteHeights

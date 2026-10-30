/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointNamedParents
public import LeanCanny.Encoding.FlatAffineEndpointMarkerComplete

/-! # Every endpoint point supplies an actual native parent name

Marker completeness and exact rational recovery cover the entire endpoint
fiber. This includes isolated endpoint points absent from neighboring slabs.
No regularity assumption or supplied sample of a neighboring fiber is used.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointNamedParents
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem endpoint_complete (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s aWord : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input
      (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord)
    (x : Fin (count F (pairFst (pairFst s))) → ℝ)
    (hx : x ∈ FlatAffineEndpointFiniteMatching.endpointFiber F height s
      ((SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input
        (FlatAffineEndpointAdjacentSamples.heightSource F cone height)) (pairFst s) aWord ha).val (0 : Fin 1))) :
    ∃ p : NamedRationalParents.Root (source F cone height) s, ∃ w : List Bool,
      (source F cone height).descriptor s p = w ∧
      w.length ≤ (source F cone height).width s ∧
      pair s w ∈ NamedRationalParents.language (source F cone height) ∧
      ∀ i : Fin (count F (pairFst (pairFst s))),
        RationalCoordinateFamily.point (source F cone height).coordinates s p.val i.val = x i := by
  obtain ⟨w, hw, _, hcopy⟩ := FlatAffineEndpointMarkers.complete F cone height s aWord hs ha x hx
  let a := SquareSampleNamedParents.root (FlatAffineEndpointFiniteSample.input F cone height) s w hw
  let p : NamedRationalParents.Root (source F cone height) s := ⟨a.val, hs, a.property⟩
  have he : (source F cone height).descriptor s p = w :=
    SquareSampleNamedParents.word_root _ (FlatAffineEndpointFiniteSample.complete F cone height) s w hw
  refine ⟨p, w, he, ?_, ?_, ?_⟩
  · rw [← he]
    exact (source F cone height).descriptor_length s p
  · rw [← he]
    exact NamedRationalParents.descriptor_valid (source F cone height) s p
  · intro i
    have H := coordinates_point F cone height s p.val i
    have D := congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 1 i)
      (SquareSampleCompleteParameterTest.decode_theta (FlatAffineEndpointFiniteSample.input F cone height) s w hw)
    exact H.trans (D.trans (congrFun hcopy i))

end LeanCanny.Encoding.FlatAffineEndpointNamedParents

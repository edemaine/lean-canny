/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointAlgebraicMarker
public import LeanCanny.Encoding.SquareSampleNamedParents

/-! # Native named parents for actual endpoint point markers

The complete joint label remains the parent's name. Its source frame is
checked, and its rational ambient coordinates are precisely the designated
endpoint copy. The separable primitive equation and native derivative probes
supply the existing recursive child interface at singular original endpoints.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineEndpointNamedParents
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def coordinateQuery (F : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst q) (FlatAffineEndpointCopyEquality.slotWord F 1 (pairFst q) (pairSnd q))
theorem coordinateQuery_FP {F : Inputs} (h : F.Access) : coordinateQuery F ∈ FP :=
  mem_FP_pair pairFst_mem_FP (FlatAffineEndpointCopyEquality.slotWord_FP h 1)
theorem coordinateQuery_source (F : Inputs) (q : List Bool) : pairFst (coordinateQuery F q) = id (pairFst q) :=
  pairFst_pair _ _

theorem coordinateQuery_packet (F : Inputs) (s d : List Bool) :
    coordinateQuery F (pair s d) = pair s (BinaryNatCode.encode
      (FlatAffineEndpointFiniteProjection.slot F s 1 (FlatAffineEndpointFiniteSide.coordinate F s d)).val) := by
  simp only [coordinateQuery, pairFst_pair, pairSnd_pair]
  rfl

noncomputable def rawCoordinates (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : RationalCoordinateFamily.Family :=
  RationalCoordinateFamily.reindex (SquareSampleRationalCoordinates.coordinates (FlatAffineEndpointFiniteSample.input F cone height))
    id (coordinateQuery F) (coordinateQuery_source F)
noncomputable def coordinates (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : RationalCoordinateFamily.Family :=
  RationalCoordinateFamily.extend (rawCoordinates F cone height) (FlatAffineEndpointFiniteSide.originalCount F)

theorem coordinatesAccess {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    RationalCoordinateFamily.Access (coordinates F cone height) :=
  RationalCoordinateFamily.extend_access
    (RationalCoordinateFamily.reindex_access
      (SquareSampleRationalCoordinates.coordinatesAccess (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh))
      id (coordinateQuery F) (coordinateQuery_source F) id_mem_FP (coordinateQuery_FP h))
    (BinaryFn.ofUnary (FlatAffineEndpointFiniteSide.originalCount_unary h))

theorem coordinates_defined (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (a : ℝ)
    (ha : (SquareSampleCoordinates.parameter (FlatAffineEndpointFiniteSample.input F cone height) s).eval₂ (Int.castRingHom ℝ) a = 0) :
    RationalCoordinateFamily.Defined (coordinates F cone height) s a := by
  have H := SquareSampleRationalCoordinates.defined (FlatAffineEndpointFiniteSample.input F cone height) s a ha
  apply RationalCoordinateFamily.extend_defined
  intro i _
  simpa only [rawCoordinates, RationalCoordinateFamily.reindex, Function.comp_apply, coordinateQuery_packet] using
      H (FlatAffineEndpointFiniteProjection.slot F s 1 (FlatAffineEndpointFiniteSide.coordinate F s (BinaryNatCode.encode i))).val

theorem coordinates_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (a : ℝ)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :
    RationalCoordinateFamily.point (coordinates F cone height) s a i.val =
      FlatAffineEndpointFiniteProjection.copy F s
        (SquareSampleParameters.decode (FlatAffineEndpointFiniteSample.input F cone height) s a) 1 i := by
  rw [coordinates, RationalCoordinateFamily.extend_point, ite_eq_left i.isLt]
  have H := SquareSampleRationalCoordinates.point (FlatAffineEndpointFiniteSample.input F cone height) s a
    (FlatAffineEndpointFiniteProjection.slot F s 1 i)
  simpa only [RationalCoordinateFamily.point, rawCoordinates, RationalCoordinateFamily.reindex,
    Function.comp_apply, coordinateQuery_packet, FlatAffineEndpointFiniteSide.coordinate_encode,
    FlatAffineEndpointFiniteProjection.copy, FlatAffineEndpointFiniteProjection.slot] using H

attribute [local irreducible] SquareSampleNamedParents.derivativeValue SquareSampleCompleteParameterTest.value

noncomputable def source (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : NamedRationalParents.Source where
  equation := SquareSampleRationalCoordinates.equation (FlatAffineEndpointFiniteSample.input F cone height)
  coordinates := coordinates F cone height
  roots s := {a | FlatAffineEndpointFiniteFrame.Valid F height s ∧
    a ∈ SquareSampleNamedParents.roots (FlatAffineEndpointFiniteSample.input F cone height) s}
  root_zero _ _ ha := ha.2.1
  defined s a ha := coordinates_defined F cone height s a ha.2.1
  descriptor s a := SquareSampleNamedParents.word (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height) s ⟨a.val, a.property.2⟩
  descriptor_injective s _x _y he := Subtype.ext (congrArg
    (fun z : SquareSampleNamedParents.Root (FlatAffineEndpointFiniteSample.input F cone height) s => z.val)
    ((SquareSampleNamedParents.source (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointFiniteSample.complete F cone height)).descriptor_injective s he))
  width := SquareSampleCompleteVertices.width (FlatAffineEndpointFiniteSample.input F cone height)
  descriptor_length s a := (Classical.choose (SquareSampleNamedParents.word_valid _
    (FlatAffineEndpointFiniteSample.complete F cone height) s ⟨a.val, a.property.2⟩)).1.le
  derivativeValue := SquareSampleNamedParents.derivativeValue (FlatAffineEndpointFiniteSample.input F cone height)
  derivative_packet s a k := (SquareSampleNamedParents.source (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointFiniteSample.complete F cone height)).derivative_packet s ⟨a.val, a.property.2⟩ k

theorem language_iff (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool) :
    q ∈ NamedRationalParents.language (source F cone height) ↔
      q ∈ GuardedSquareSampleInput.language (FlatAffineEndpointFiniteSample.data F cone height) := by
  change (∃ a : {a : ℝ // FlatAffineEndpointFiniteFrame.Valid F height (pairFst q) ∧
      a ∈ SquareSampleNamedParents.roots (FlatAffineEndpointFiniteSample.input F cone height) (pairFst q)},
    SquareSampleNamedParents.word (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointFiniteSample.complete F cone height) (pairFst q) ⟨a.val, a.property.2⟩ = pairSnd q) ↔ _
  unfold GuardedSquareSampleInput.language
  change _ ↔ FlatAffineEndpointFiniteFrame.Valid F height (pairFst q) ∧
    SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) (pairFst q) (pairSnd q)
  constructor
  · rintro ⟨a, ha⟩
    have H := SquareSampleNamedParents.word_valid (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointFiniteSample.complete F cone height) (pairFst q) ⟨a.val, a.property.2⟩
    rw [ha] at H
    exact ⟨a.property.1, H⟩
  · rintro ⟨hs, hw⟩
    let a := SquareSampleNamedParents.root (FlatAffineEndpointFiniteSample.input F cone height) (pairFst q) (pairSnd q) hw
    exact ⟨⟨a.val, hs, a.property⟩, SquareSampleNamedParents.word_root _ (FlatAffineEndpointFiniteSample.complete F cone height) _ _ hw⟩

theorem access {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    NamedRationalParents.Access (source F cone height) := by
  refine ⟨SquareSampleRationalCoordinates.equationAccess (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh),
    coordinatesAccess h cone height hh, FlatAffineEndpointFiniteSample.width_unary h cone height hh, ?_,
    SquareSampleNamedParents.derivativeEvaluator (FlatAffineEndpointFiniteSample.sampleAccess h cone height hh)⟩
  apply (GuardedSquareSampleInput.decider (FlatAffineEndpointFiniteSample.access h cone height hh)).congr
  ext q
  exact (language_iff F cone height q).symm

noncomputable def markerRoot (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height) : NamedRationalParents.Root (source F cone height) (FlatAffineEndpointMarkers.source q) :=
  ⟨SquareSampleCompleteParameterTest.theta (FlatAffineEndpointFiniteSample.input F cone height)
    (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q),
    FlatAffineEndpointMarkers.frame_valid F cone height q hq,
    (SquareSampleNamedParents.root (FlatAffineEndpointFiniteSample.input F cone height)
      (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q)
      (FlatAffineEndpointMarkers.joint_valid F cone height q hq)).property⟩

theorem marker_name (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height) :
    (source F cone height).descriptor (FlatAffineEndpointMarkers.source q) (markerRoot F cone height q hq) =
      FlatAffineEndpointMarkers.jointWord q :=
  SquareSampleNamedParents.word_root _ (FlatAffineEndpointFiniteSample.complete F cone height) _ _
    (FlatAffineEndpointMarkers.joint_valid F cone height q hq)

theorem marker_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (q : List Bool)
    (hq : q ∈ FlatAffineEndpointMarkers.language F cone height)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F (FlatAffineEndpointMarkers.source q))) :
    RationalCoordinateFamily.point (source F cone height).coordinates (FlatAffineEndpointMarkers.source q)
      (markerRoot F cone height q hq).val i.val =
      FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointMarkers.source q)
        (SquareSampleCompleteVertices.candidate (FlatAffineEndpointFiniteSample.input F cone height)
          (FlatAffineEndpointMarkers.source q) (FlatAffineEndpointMarkers.jointWord q)
          (FlatAffineEndpointMarkers.joint_valid F cone height q hq)).val 1 i := by
  exact (coordinates_point F cone height (FlatAffineEndpointMarkers.source q) _ i).trans
    (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F (FlatAffineEndpointMarkers.source q) z 1 i)
      (SquareSampleCompleteParameterTest.decode_theta _ _ _ (FlatAffineEndpointMarkers.joint_valid F cone height q hq)))

end LeanCanny.Encoding.FlatAffineEndpointNamedParents

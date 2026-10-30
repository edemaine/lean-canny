/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineEndpointNamedParents
public import LeanCanny.Encoding.FlatAffineEndpointRankWordSample

/-! # Native named parents at actual interior sample points

The original joint label remains the ancestry name, while its rational
coordinates select the current spatial copy. This supplies recursive slice
queries at interior samples, where endpoint-copy parents denote other points.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineCurrentNamedParents
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def coordinateQuery (F : Inputs) (q : List Bool) : List Bool :=
  pair (pairFst q) (FlatAffineEndpointCopyEquality.slotWord F 0 (pairFst q) (pairSnd q))
theorem coordinateQuery_FP {F : Inputs} (h : F.Access) : coordinateQuery F ∈ FP :=
  mem_FP_pair pairFst_mem_FP (FlatAffineEndpointCopyEquality.slotWord_FP h 0)
theorem coordinateQuery_source (F : Inputs) (q : List Bool) : pairFst (coordinateQuery F q) = id (pairFst q) :=
  pairFst_pair _ _
theorem coordinateQuery_packet (F : Inputs) (s d : List Bool) :
    coordinateQuery F (pair s d) = pair s (BinaryNatCode.encode
      (FlatAffineEndpointFiniteProjection.slot F s 0 (FlatAffineEndpointFiniteSide.coordinate F s d)).val) := by
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
    H (FlatAffineEndpointFiniteProjection.slot F s 0 (FlatAffineEndpointFiniteSide.coordinate F s (BinaryNatCode.encode i))).val

theorem coordinates_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s : List Bool) (a : ℝ)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :
    RationalCoordinateFamily.point (coordinates F cone height) s a i.val =
      FlatAffineEndpointFiniteProjection.copy F s (SquareSampleParameters.decode (FlatAffineEndpointFiniteSample.input F cone height) s a) 0 i := by
  rw [coordinates, RationalCoordinateFamily.extend_point, ite_eq_left i.isLt]
  have H := SquareSampleRationalCoordinates.point (FlatAffineEndpointFiniteSample.input F cone height) s a
    (FlatAffineEndpointFiniteProjection.slot F s 0 i)
  simpa only [RationalCoordinateFamily.point, rawCoordinates, RationalCoordinateFamily.reindex,
    Function.comp_apply, coordinateQuery_packet, FlatAffineEndpointFiniteSide.coordinate_encode,
    FlatAffineEndpointFiniteProjection.copy, FlatAffineEndpointFiniteProjection.slot] using H

attribute [local irreducible] SquareSampleNamedParents.derivativeValue SquareSampleCompleteParameterTest.value

theorem access_with_coordinates (P : NamedRationalParents.Source) (C : RationalCoordinateFamily.Family)
    (hC : ∀ s a, a ∈ P.roots s → RationalCoordinateFamily.Defined C s a)
    (A : NamedRationalParents.Access P) (B : RationalCoordinateFamily.Access C) :
    NamedRationalParents.Access ({ P with coordinates := C, defined := hC } : NamedRationalParents.Source) :=
  ⟨A.equation, B, A.width, A.validity, A.derivative⟩

noncomputable def source (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) : NamedRationalParents.Source :=
  { FlatAffineEndpointNamedParents.source F cone height with
    coordinates := coordinates F cone height
    defined := fun s a ha => coordinates_defined F cone height s a ha.2.1 }

theorem access {F : Inputs} (h : F.Access) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (hh : UnaryFn (fun u => (height u).val)) :
    NamedRationalParents.Access (source F cone height) := by
  exact access_with_coordinates _ _ _ (FlatAffineEndpointNamedParents.access h cone height hh)
    (coordinatesAccess h cone height hh)

noncomputable def root (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool)
    (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w) :
    NamedRationalParents.Root (source F cone height) s :=
  ⟨SquareSampleCompleteParameterTest.theta (FlatAffineEndpointFiniteSample.input F cone height) s w, hs,
    (SquareSampleNamedParents.root (FlatAffineEndpointFiniteSample.input F cone height) s w hw).property⟩

theorem root_name (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w) :
    (source F cone height).descriptor s (root F cone height s w hs hw) = w :=
  SquareSampleNamedParents.word_root _ (FlatAffineEndpointFiniteSample.complete F cone height) s w hw

theorem root_point (F : Inputs) (cone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (s w : List Bool) (hs : FlatAffineEndpointFiniteFrame.Valid F height s)
    (hw : SquareSampleCompleteVertices.Valid (FlatAffineEndpointFiniteSample.input F cone height) s w)
    (i : Fin (FlatAffineEndpointFiniteSide.originalCount F s)) :
    RationalCoordinateFamily.point (source F cone height).coordinates s (root F cone height s w hs hw).val i.val =
      FlatAffineEndpointRankWord.currentValue F cone height s w i := by
  exact (coordinates_point F cone height s _ i).trans
    ((congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0 i)
      (SquareSampleCompleteParameterTest.decode_theta _ s w hw)).trans
      (congrArg (fun z => FlatAffineEndpointFiniteProjection.copy F s z 0 i)
        (FlatAffineEndpointRankWord.anchorPoint_packet F cone height s w hw)).symm)

end LeanCanny.Encoding.FlatAffineCurrentNamedParents

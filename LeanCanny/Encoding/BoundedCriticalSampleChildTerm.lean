/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildReaders
public import LeanCanny.Encoding.BoundedCriticalSampleBlockCoefficient
public import LeanCanny.Encoding.BoundedCriticalSampleChildTestMoments

/-! # Original arithmetic terms pulled back to child parameters

The source term first retains the parent sample outside the free coordinate
block, then substitutes the child's rational joint coordinates. Both rounds
of denominator clearing use even powers. The source and both coordinate
readers, including their binary degree and mass bounds, are constructed.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildTerm
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open BoundedCriticalSampleChildSource (Inputs count)
open BoundedCriticalSampleChildReaders (numerator denominator)
open BoundedCriticalSampleChildCoordinates (coordinateDegree coordinateMass parameter)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleBlockTerm.polynomial
  BoundedCriticalSampleBlockEncoding.width BoundedCriticalSampleBlockTerm.mass
  BoundedCriticalSampleChildCoordinates.coordinate

noncomputable def family (F : Inputs) (read : List Bool → List Bool) :
    FixedWidthRationalSubstitutionBits.Family where
  arity := count F
  width := BoundedCriticalSampleBlockEncoding.width F.parent read
  source := BoundedCriticalSampleBlockTerm.polynomial F.parent read F.offset F.dim
  numerator := numerator F
  denominator := denominator F
  degree_fit u i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((BoundedCriticalSampleBlockTerm.polynomial_degree F.parent read F.offset F.dim u).trans_lt
      (BoundedCriticalSampleBlockEncoding.clearing_lt F.parent read u))

noncomputable def polynomial (F : Inputs) (read : List Bool → List Bool) : List Bool → Polynomial ℤ :=
  (family F read).polynomial

noncomputable def access {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    FixedWidthRationalSubstitutionBits.Access (family F read) where
  arity := BoundedCriticalSampleChildSource.count_unary h
  width := BoundedCriticalSampleBlockEncoding.width_unary h.parent read hr
  coefficient := BoundedCriticalSampleBlockCoefficient.value F.parent read F.offset F.dim
  evaluator := BoundedCriticalSampleBlockCoefficient.evaluator h.parent read hr h.offset h.dim h.arity
  coefficient_eq u r _ m hm := by
    simpa only [family, FixedWidthRationalSubstitutionBits.Family.coefficient,
      FixedWidthPolynomial.nativeExponent_refl, count] using
      BoundedCriticalSampleBlockCoefficient.packet F.parent read F.offset F.dim u r m hm
  coordinates := BoundedCriticalSampleChildReaders.readers h

theorem evaluator {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    SpaceFunction (PrimitivePairBits.coefficient (polynomial F read)) :=
  (access h read hr).polynomialEvaluator

noncomputable def degree (F : Inputs) (read : List Bool → List Bool) : List Bool → ℕ :=
  (family F read).degree (coordinateDegree F)
noncomputable def sourceMass (F : Inputs) (read : List Bool → List Bool) (u : List Bool) : ℕ :=
  BoundedCriticalSampleBlockEncoding.span F.parent read F.dim u + BoundedCriticalSampleBlockTerm.mass F.parent read u
noncomputable def mass (F : Inputs) (read : List Bool → List Bool) : List Bool → ℕ :=
  (family F read).mass (sourceMass F read) (coordinateMass F)

theorem source_mass (F : Inputs) (read : List Bool → List Bool) (u : List Bool) :
    MvMass.mass ((family F read).source u) ≤ 2 ^ sourceMass F read u :=
  BoundedCriticalSampleBlockTerm.polynomial_mass F.parent read F.offset F.dim u

theorem polynomial_degree (F : Inputs) (read : List Bool → List Bool) (u : List Bool) :
    (polynomial F read u).natDegree ≤ degree F read u :=
  (family F read).polynomial_degree (coordinateDegree F)
    (fun v i _ => (BoundedCriticalSampleChildReaders.coordinate_bounds F v i).1)
    (fun v i _ => (BoundedCriticalSampleChildReaders.coordinate_bounds F v i).2.1) u

theorem polynomial_mass (F : Inputs) (read : List Bool → List Bool) (u : List Bool) :
    coefficientMass (polynomial F read u) ≤ 2 ^ mass F read u :=
  (family F read).polynomial_mass (sourceMass F read) (coordinateMass F)
    (fun v _ _ => (MvMass.coeff_le _ _).trans (source_mass F read v))
    (fun v i _ => (BoundedCriticalSampleChildReaders.coordinate_bounds F v i).2.2.1)
    (fun v i _ => (BoundedCriticalSampleChildReaders.coordinate_bounds F v i).2.2.2) u

theorem degree_binary {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (degree F read) :=
  (access h read hr).degree_binary (BoundedCriticalSampleChildCoordinates.coordinateDegree_binary h)

theorem sourceMass_binary {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (sourceMass F read) :=
  BoundedCriticalSampleBlockTerm.polynomial_mass_binary h.parent read hr h.dim

theorem mass_binary {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    BinaryFn (mass F read) :=
  (access h read hr).mass_binary (sourceMass_binary h read hr)
    (BoundedCriticalSampleChildCoordinates.coordinateMass_binary h)

noncomputable def test (F : Inputs) (read : List Bool → List Bool) : BoundedCriticalSampleChildTestMoments.Test where
  polynomial := polynomial F read
  degree := degree F read
  mass := mass F read
  polynomial_degree := polynomial_degree F read
  polynomial_mass := polynomial_mass F read

noncomputable def testAccess {F : Inputs} (h : F.PolyTime) (read : List Bool → List Bool) (hr : read ∈ FP) :
    (test F read).Access :=
  BoundedCriticalSampleChildTestMoments.Test.Access.ofPrimitive (degree_binary h read hr)
    (mass_binary h read hr) (evaluator h read hr)

theorem sign_decode (F : Inputs) (read : List Bool → List Bool) (u : List Bool) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F read u).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((BoundedCriticalSampleBlockTerm.polynomial F.parent read F.offset F.dim u).eval₂
        (Int.castRingHom ℝ) (BoundedCriticalSampleChildParameters.decode F u theta)) :=
  (family F read).sign u theta (fun i => BoundedCriticalSampleChildReaders.denominator_ne_zero F u theta ht i)

end LeanCanny.Encoding.BoundedCriticalSampleChildTerm

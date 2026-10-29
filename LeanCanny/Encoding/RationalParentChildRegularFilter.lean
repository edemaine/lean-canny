/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildJacobianCoefficient
public import LeanCanny.Encoding.RationalParentChildReaders
public import LeanCanny.Encoding.RationalParentChildFilters

/-! # A native regularity filter on child parameter roots

Even denominator clearing turns the actual joint Jacobian into a univariate
integer polynomial. Nonvanishing is exactly analytic regularity on parameter
roots. Coefficients and all degree and mass controls are native.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildRegularFilter
open LeanCanny.Algebra LeanCanny.Computation
open RationalParentChildSource (Inputs count)
open RationalParentChildCoordinates (parameter coordinateDegree coordinateMass)
open RationalParentChildReaders (numerator denominator)
open RationalParentChildParameters (system decode)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildJacobianSource.polynomial RationalParentChildJacobianSource.width
  RationalParentChildJacobianSource.mass RationalParentChildCoordinates.coordinate

noncomputable def family (F : Inputs) : FixedWidthRationalSubstitutionBits.Family where
  arity := count F
  width := RationalParentChildJacobianSource.width F
  source := RationalParentChildJacobianSource.polynomial F
  numerator := numerator F
  denominator := denominator F
  degree_fit u i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt
    ((RationalParentChildJacobianSource.polynomial_degree F u).trans_lt
      (RationalParentChildJacobianSource.degree_lt_width F u))

noncomputable def polynomial (F : Inputs) : List Bool → Polynomial ℤ := (family F).polynomial

noncomputable def access {F : Inputs} (h : F.Access) : FixedWidthRationalSubstitutionBits.Access (family F) where
  arity := RationalParentChildSource.count_unary h
  width := RationalParentChildJacobianSource.width_unary h
  coefficient := RationalParentChildJacobianCoefficient.value F
  evaluator := RationalParentChildJacobianCoefficient.evaluator h
  coefficient_eq u r hr m hm := RationalParentChildJacobianCoefficient.packet F u r m hm hr
  coordinates := RationalParentChildReaders.readers h

theorem evaluator {F : Inputs} (h : F.Access) : SpaceFunction (PrimitivePairBits.coefficient (polynomial F)) :=
  (access h).polynomialEvaluator

theorem nonzero_iff (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ) theta ≠ 0 ↔
      (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) (decode F u theta)).IsInvertible := by
  have H := (family F).zero_iff u theta (fun i => RationalParentChildReaders.denominator_ne_zero F u theta ht i)
  exact (not_congr H).trans (RationalParentChildJacobianSource.eval_ne_zero_iff F u (decode F u theta))

theorem sign (F : Inputs) (u : List Bool) (theta : ℝ)
    (ht : (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign ((polynomial F u).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((RationalParentChildJacobianSource.polynomial F u).eval₂ (Int.castRingHom ℝ) (decode F u theta)) :=
  (family F).sign u theta (fun i => RationalParentChildReaders.denominator_ne_zero F u theta ht i)

noncomputable def degree (F : Inputs) := (family F).degree (coordinateDegree F)
noncomputable def mass (F : Inputs) :=
  (family F).mass (RationalParentChildJacobianSource.mass F) (coordinateMass F)

theorem degree_binary {F : Inputs} (h : F.Access) : BinaryFn (degree F) :=
  (access h).degree_binary (RationalParentChildCoordinates.coordinateDegree_binary h)
theorem mass_binary {F : Inputs} (h : F.Access) : BinaryFn (mass F) :=
  (access h).mass_binary (RationalParentChildJacobianSource.mass_binary h)
    (RationalParentChildCoordinates.coordinateMass_binary h)

theorem polynomial_degree (F : Inputs) (u : List Bool) : (polynomial F u).natDegree ≤ degree F u :=
  (family F).polynomial_degree (coordinateDegree F)
    (fun c i _ => (RationalParentChildReaders.coordinate_bounds F c i).1)
    (fun c i _ => (RationalParentChildReaders.coordinate_bounds F c i).2.1) u

theorem polynomial_mass (F : Inputs) (u : List Bool) : coefficientMass (polynomial F u) ≤ 2 ^ mass F u :=
  (family F).polynomial_mass (RationalParentChildJacobianSource.mass F) (coordinateMass F)
    (fun c _ _ => (MvMass.coeff_le _ _).trans (RationalParentChildJacobianSource.polynomial_mass F c))
    (fun c i _ => (RationalParentChildReaders.coordinate_bounds F c i).2.2.1)
    (fun c i _ => (RationalParentChildReaders.coordinate_bounds F c i).2.2.2) u

theorem regular_iff (F : Inputs) (u : List Bool) (theta : ℝ) :
    RationalParentChildFilters.Valid F u theta ∧ (polynomial F u).eval₂ (Int.castRingHom ℝ) theta ≠ 0 ↔
      (parameter F u).eval₂ (Int.castRingHom ℝ) theta = 0 ∧
        (∀ i, (system F u i).eval₂ (Int.castRingHom ℝ) (decode F u theta) = 0) ∧
          (fderiv ℝ (fun y => fun i => (system F u i).eval₂ (Int.castRingHom ℝ) y) (decode F u theta)).IsInvertible := by
  constructor
  · rintro ⟨⟨ht, hz⟩, hr⟩
    exact ⟨ht, hz, (nonzero_iff F u theta ht).mp hr⟩
  · rintro ⟨ht, hz, hr⟩
    exact ⟨⟨ht, hz⟩, (nonzero_iff F u theta ht).mpr hr⟩

end LeanCanny.Encoding.RationalParentChildRegularFilter

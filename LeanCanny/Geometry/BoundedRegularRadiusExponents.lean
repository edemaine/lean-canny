/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.BoundedRegularSource

/-! # The regular-source coefficient exponents are affine in the radius code

Thus every dyadic coefficient is a fixed integer times a fixed power of the
physical radius `2^R`. The slopes depend only on dimension and spatial degree.
This is algebraic parameter groundwork, with no stabilization claim.
-/
@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularRadius
open LeanCanny.Algebra LeanCanny.Encoding

def perturbationSlope (n D : ℕ) : ℕ :=
  16*CoerciveCoordinateEliminant.columnBound (n+3) (2*BoundedZeroSource.degreeAllowance D)+BoundedZeroSource.powerDegree D
def sourceMassSlope (n D : ℕ) : ℕ := perturbationSlope n D+4+BoundedZeroSource.powerDegree D
def regularizationSlope (n D : ℕ) : ℕ :=
  FixedWidthPolynomial.count (n+6) (FermatRegularSource.width (n+3) (BoundedZeroSource.powerDegree D))*sourceMassSlope n D

theorem mass_affine (n b R : ℕ) :
    BoundedZeroSource.massExponent n b R=BoundedZeroSource.massExponent n b 0+4*R := by
  unfold BoundedZeroSource.massExponent BoundedZeroSource.barrierMassExponent
  ring

theorem penalty_affine (n D R : ℕ) :
    BoundedZeroSource.penaltyExponent n D R=BoundedZeroSource.penaltyExponent n D 0+
      BoundedZeroSource.powerDegree D*R := by
  unfold BoundedZeroSource.penaltyExponent
  ring

theorem critical_value_exponent_add (n D b c : ℕ) :
    GeneralCriticalValueBounds.exponent n D (b+c)=GeneralCriticalValueBounds.exponent n D b+
      4*CoerciveCoordinateEliminant.columnBound (n+1) (2*D)*c := by
  unfold GeneralCriticalValueBounds.exponent GeneralCriticalValueBounds.massExponent
    CoerciveRadiusBits.massExponent CoerciveRadiusBits.budgetExponent
  ring

theorem perturbation_affine (n D b R : ℕ) :
    BoundedZeroSource.perturbationExponent n D b R=BoundedZeroSource.perturbationExponent n D b 0+
      perturbationSlope n D*R := by
  unfold BoundedZeroSource.perturbationExponent BoundedPositivePerturbation.exponent
  rw [mass_affine n b R,critical_value_exponent_add,penalty_affine n D R]
  unfold perturbationSlope
  ring

theorem source_mass_affine (n D b R : ℕ) :
    BoundedRegularSource.sourceMassExponent n D b R=BoundedRegularSource.sourceMassExponent n D b 0+
      sourceMassSlope n D*R := by
  unfold BoundedRegularSource.sourceMassExponent BoundedRegularSource.lowMassExponent
  rw [perturbation_affine n D b R,mass_affine n b R,penalty_affine n D R]
  unfold sourceMassSlope
  ring

theorem regularization_affine (n D b R : ℕ) :
    BoundedRegularSource.regularizationExponent n D b R=BoundedRegularSource.regularizationExponent n D b 0+
      regularizationSlope n D*R := by
  unfold BoundedRegularSource.regularizationExponent IntegerRegularSource.exponent
    CriticalRegularLevel.exponent CriticalRegularLevel.massBits CriticalRegularLevel.coefficientBits
  rw [source_mass_affine n D b R]
  unfold regularizationSlope
  ring

end LeanCanny.Geometry.BoundedRegularRadius

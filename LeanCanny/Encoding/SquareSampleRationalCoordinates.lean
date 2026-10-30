/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.SquareSampleCompleteParameterTest
public import LeanCanny.Algebra.RationalCoordinateFamily
public import LeanCanny.Algebra.SeparablePolynomialFamily

/-! # Complete square-system parameters as native rational ambient parents -/

@[expose] public section
namespace LeanCanny.Encoding.SquareSampleRationalCoordinates
open LeanCanny.Algebra LeanCanny.Computation
open SquareSampleInput (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def equation (F : Inputs) : SeparablePolynomialFamily.Source where
  polynomial := SquareSampleCoordinates.parameter F
  degree := SquareSampleCoordinates.parameterDegree F
  mass := SquareSampleCoordinates.baseHeight F
  degree_le c := (SquareSampleCoordinates.parameter_bounds F c).1
  mass_le c := (SquareSampleCoordinates.parameter_bounds F c).2
  separable c := SquareSampleCoordinates.parameter_separable F c

theorem equationAccess {F : Inputs} (h : F.Access) : SeparablePolynomialFamily.Access (equation F) :=
  ⟨SquareSampleCoordinates.parameterDegree_binary h, SquareSampleCoordinates.baseHeight_binary h,
    SquareSampleCoordinates.parameter_coefficient_evaluator h⟩

noncomputable def raw (F : Inputs) : RationalCoordinateFamily.Family where
  coordinate := SquareSampleCoordinates.coordinate F
  degree := SquareSampleCoordinates.coordinateDegree F
  mass := SquareSampleCoordinates.coordinateMass F
  degree_le q := (SquareSampleCoordinates.coordinate_bounds F q).1
  numerator_mass q := (SquareSampleCoordinates.coordinate_bounds F q).2.1
  denominator_mass q := (SquareSampleCoordinates.coordinate_bounds F q).2.2

theorem rawAccess {F : Inputs} (h : F.Access) : RationalCoordinateFamily.Access (raw F) :=
  ⟨SquareSampleCoordinates.coordinateDegree_binary h, SquareSampleCoordinates.coordinateMass_binary h,
    (SquareSampleCoordinates.coefficient_evaluators h).1, (SquareSampleCoordinates.coefficient_evaluators h).2⟩

noncomputable def coordinates (F : Inputs) : RationalCoordinateFamily.Family := RationalCoordinateFamily.extend (raw F) F.count
theorem coordinatesAccess {F : Inputs} (h : F.Access) : RationalCoordinateFamily.Access (coordinates F) :=
  RationalCoordinateFamily.extend_access (rawAccess h) (BinaryFn.ofUnary h.count)

theorem defined (F : Inputs) (c : List Bool) (a : ℝ)
    (ha : ((equation F).polynomial c).eval₂ (Int.castRingHom ℝ) a = 0) :
    RationalCoordinateFamily.Defined (coordinates F) c a :=
  RationalCoordinateFamily.extend_defined (raw F) F.count c a (fun i hi =>
    (SquareSampleCoordinates.parameter_root_coordinates F c a ha ⟨i, hi⟩).1)

theorem point (F : Inputs) (c : List Bool) (a : ℝ) (i : Fin (F.count c)) :
    RationalCoordinateFamily.point (coordinates F) c a i.val = SquareSampleParameters.decode F c a i := by
  rw [coordinates, RationalCoordinateFamily.extend_point, ite_eq_left i.isLt]
  rfl

end LeanCanny.Encoding.SquareSampleRationalCoordinates

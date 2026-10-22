/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeCoefficientDecomposition
public import LeanCanny.Algebra.EmbeddedCoefficient
public import LeanCanny.Algebra.ProjectionCoefficientFormula

/-! # Tube coefficients need only three dense source queries

The source-square term needs one coefficient. Each of the two linear-shift
terms needs one shifted source coefficient. All remaining contributions are
coefficients of the zero-source tube, containing only sparse constraints.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial
open scoped BigOperators

variable {ι : Type*}

def spatialEmbedding : ι → IntegerCoordinate ι := fun i => .inl (.inl i)

theorem spatialEmbedding_injective : Function.Injective (spatialEmbedding (ι := ι)) :=
  Sum.inl_injective.comp Sum.inl_injective

noncomputable def spatialCoefficient (p : MvPolynomial ι ℤ) (m : IntegerCoordinate ι →₀ ℕ) : ℤ :=
  Algebra.EmbeddedCoefficient.value spatialEmbedding spatialEmbedding_injective p m

noncomputable def shiftedSpatialCoefficient (p : MvPolynomial ι ℤ) (m : IntegerCoordinate ι →₀ ℕ) (b : Bool) : ℤ := by
  classical
  exact if (.inl (.inr (.inl b)) : IntegerCoordinate ι) ∈ m.support then
    spatialCoefficient p (m - Finsupp.single (.inl (.inr (.inl b))) 1) else 0

theorem coeff_integerSpatial (p : MvPolynomial ι ℤ) (m : IntegerCoordinate ι →₀ ℕ) :
    (integerSpatial p).coeff m = spatialCoefficient p m :=
  Algebra.EmbeddedCoefficient.coeff_rename spatialEmbedding spatialEmbedding_injective p m

theorem coeff_integerSpatial_linear (p : MvPolynomial ι ℤ) (m : IntegerCoordinate ι →₀ ℕ) (b : Bool) :
    (integerSpatial p * sourceLinear (.inl b)).coeff m = (if b then -2 else 2) * shiftedSpatialCoefficient p m b := by
  classical
  have hshift : Algebra.EmbeddedCoefficient.shift (integerSpatial p) m (.inl (.inr (.inl b))) =
      shiftedSpatialCoefficient p m b := by
    unfold Algebra.EmbeddedCoefficient.shift shiftedSpatialCoefficient
    simp only [coeff_integerSpatial]
  cases b <;> simp only [sourceLinear, Algebra.EmbeddedCoefficient.coeff_mul_C_X, hshift, Bool.false_eq_true,
    ite_false, ite_true]

variable [Fintype ι] [DecidableEq ι]

theorem coeff_integerPolynomial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (m : IntegerCoordinate ι →₀ ℕ) :
    (integerPolynomial p s).coeff m = squareMultiplicity s * spatialCoefficient (p ^ 2) m +
      (if Sum.inl false ∈ s then 2 * shiftedSpatialCoefficient p m false else 0) +
      (if Sum.inl true ∈ s then -2 * shiftedSpatialCoefficient p m true else 0) +
      (integerPolynomial (0 : MvPolynomial ι ℤ) s).coeff m := by
  classical
  have hf := coeff_integerSpatial_linear p m false
  have ht := coeff_integerSpatial_linear p m true
  simp only [sourceLinear, Bool.false_eq_true, ite_false, ite_true] at hf ht
  rw [integerPolynomial_decomposition, linearShift_eq]
  split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply, MvPolynomial.coeff_C_mul, coeff_integerSpatial, hf, ht]
  all_goals ring

omit [DecidableEq ι] in
theorem coeff_integerProjection_level (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (m : IntegerProjectionVariable ι →₀ ℕ) :
    (integerProjection p s none).coeff m = Algebra.EmbeddedCoefficient.value
      Algebra.ProjectionFlatten.coefficientEmbedding Algebra.ProjectionFlatten.coefficientEmbedding_injective
        (integerPolynomial p s) m := by
  exact Algebra.ProjectionFlatten.coeff_level (polynomial p s) (base ι) m

omit [DecidableEq ι] in
theorem coeff_integerProjection_partial (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (i : {i : Coordinate ι // i ≠ base ι}) (m : IntegerProjectionVariable ι →₀ ℕ) :
    (integerProjection p s (some i)).coeff m = Algebra.EmbeddedCoefficient.derivative
      Algebra.ProjectionFlatten.coefficientEmbedding Algebra.ProjectionFlatten.coefficientEmbedding_injective
        (integerPolynomial p s) (.inl i.val) m -
          Algebra.ProjectionFlatten.shiftedDerivative (integerPolynomial p s) (base ι) i.val m := by
  exact Algebra.ProjectionFlatten.coeff_partial (polynomial p s) (base ι) i.val m

end LeanCanny.Geometry.TubePolynomial

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedRegularRadiusLowGrowth
public import LeanCanny.Algebra.IntegerPolynomialDyadicInterpolation

/-! # Original-only parameter mass bounds for the actual spatial source

Interpolation consumes the literal native source's proved dyadic growth.
The resulting common bound covers all parameter coefficients before radius
evaluation, including the actual leading scalar.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedRegularRadiusLowModel
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation Polynomial

def sourceMassBudget (n D : ℕ) :=
  IntegerPolynomialDyadic.massBudget 0 (heightSlope n D) (heightOffset n D D)

theorem sourceMassBudget_binary {n D : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn D) :
    BinaryFn (fun q => sourceMassBudget (n q) (D q)) :=
  IntegerPolynomialDyadic.massBudget_binary (BinaryFn.const 0)
    (heightSlope_binary hn hD) (heightOffset_binary hn hD hD)

theorem low_coefficient_mass (n : ℕ) (t : ETR.Term) (e : Fin (n + 4) →₀ ℕ) :
    coefficientMass ((low (t.finitePolynomial n) t.toData.size t.toData.size).coeff e) ≤
      2 ^ sourceMassBudget n t.toData.size :=
  IntegerPolynomialDyadic.coefficientMass_le _ 0 _ _
    (fun R _ => source_coefficient_growth n t R e)

theorem leading_mass (n D b : ℕ) :
    coefficientMass (leading n D b) = 2 ^ BoundedRegularSource.regularizationExponent n D b 0 := by
  unfold leading
  rw [Polynomial.C_mul_X_pow_eq_monomial, coefficientMass_monomial, Int.natAbs_pow]
  rfl

theorem leading_mass_le (n D : ℕ) :
    coefficientMass (leading n D D) ≤ 2 ^ sourceMassBudget n D := by
  rw [leading_mass]
  apply Nat.pow_le_pow_right (by decide)
  unfold sourceMassBudget IntegerPolynomialDyadic.massBudget heightOffset
  omega

theorem source_parameter_bounds (n : ℕ) (t : ETR.Term) :
    (∀ e : Fin (n + 4) →₀ ℕ,
      coefficientMass ((low (t.finitePolynomial n) t.toData.size t.toData.size).coeff e) ≤
        2 ^ sourceMassBudget n t.toData.size ∧
      ((low (t.finitePolynomial n) t.toData.size t.toData.size).coeff e).natDegree ≤
        BoundedRegularRadius.parameterDegree n t.toData.size) ∧
    coefficientMass (leading n t.toData.size t.toData.size) ≤ 2 ^ sourceMassBudget n t.toData.size :=
  ⟨fun e => ⟨low_coefficient_mass n t e, low_coefficient_degree _ _ _ e⟩, leading_mass_le _ _⟩

end LeanCanny.Encoding.BoundedRegularRadiusLowModel

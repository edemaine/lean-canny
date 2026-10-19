/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzPower
public import LeanCanny.Algebra.PolynomialCoefficientMatrix

/-!
# Symbolic characteristic and determinant coefficients as scalar powers

For a matrix over `R[X]`, adding one bounded degree coordinate to the layered
Berkowitz matrix makes a selected coefficient an entry of a matrix power over
`R`. This is an algebraic reduction; encoded entry evaluation and its resource
certificate are separate obligations.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz
open Polynomial

variable {R : Type*} [CommRing R] {n : ℕ}

noncomputable def coefficientPower (d : ℕ) (A : Matrix (Fin n) (Fin n) R[X]) :
    Matrix (Fin (((n + 1) * (n + 1)) * (d + 1)))
      (Fin (((n + 1) * (n + 1)) * (d + 1))) R :=
  PolynomialCoefficientMatrix.finHom ((n + 1) * (n + 1)) d (powerMatrix A)

theorem coefficientPower_pow (d : ℕ) (A : Matrix (Fin n) (Fin n) R[X]) (k : Fin (n + 1)) :
    (coefficientPower d A ^ n)
      (finProdFinEquiv ((powerQuery n k).row, Fin.last d))
      (finProdFinEquiv ((powerQuery n k).col, 0)) = (A.charpoly.coeff k.val).coeff d := by
  rw [coefficientPower, PolynomialCoefficientMatrix.finHom_pow_last_zero, powerMatrix_pow]

theorem det_coeff_eq_coefficientPower (d : ℕ) (A : Matrix (Fin n) (Fin n) R[X]) :
    A.det.coeff d = (-1 : R) ^ n *
      (coefficientPower d A ^ n)
        (finProdFinEquiv ((powerQuery n 0).row, Fin.last d))
        (finProdFinEquiv ((powerQuery n 0).col, 0)) := by
  rw [coefficientPower_pow, det_eq_powerMatrix]
  have hs : (-1 : R[X]) ^ n = C ((-1 : R) ^ n) := by simp
  rw [hs, Polynomial.coeff_C_mul, powerMatrix_pow]

end LeanCanny.Algebra.Berkowitz

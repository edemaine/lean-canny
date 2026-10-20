/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Coefficients of products in separate variables

For one univariate polynomial in each coordinate, the coefficient of their
product is the product of the corresponding univariate coefficients.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparateVariableCoefficients
open MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommSemiring R]

theorem finSucc_aeval_zero (n : ℕ) (p : Polynomial R) :
    finSuccEquiv R n (Polynomial.aeval (X 0 : MvPolynomial (Fin (n + 1)) R) p) = p.map C := by
  rw [← Polynomial.aeval_algHom_apply, finSuccEquiv_X_zero, Polynomial.aeval_X_left_eq_map]
  rfl

theorem finSucc_aeval_succ (n : ℕ) (i : Fin n) (p : Polynomial R) :
    finSuccEquiv R n (Polynomial.aeval (X i.succ : MvPolynomial (Fin (n + 1)) R) p) =
      Polynomial.C (Polynomial.aeval (X i : MvPolynomial (Fin n) R) p) := by
  rw [← Polynomial.aeval_algHom_apply, finSuccEquiv_X_succ]
  exact Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom R (MvPolynomial (Fin n) R)
    (Polynomial (MvPolynomial (Fin n) R))) (X i) p

theorem coeff_prod (n : ℕ) (p : Fin n → Polynomial R) (m : Fin n →₀ ℕ) :
    (∏ i, Polynomial.aeval (X i : MvPolynomial (Fin n) R) (p i)).coeff m = ∏ i, (p i).coeff (m i) := by
  induction n with
  | zero =>
    have hm : m = 0 := Subsingleton.elim _ _
    simp [hm]
  | succ n ih =>
    rw [← Finsupp.cons_tail m, ← finSuccEquiv_coeff_coeff]
    rw [Fin.prod_univ_succ, map_mul, map_prod, finSucc_aeval_zero]
    simp only [finSucc_aeval_succ, ← map_prod]
    rw [Polynomial.coeff_mul_C, Polynomial.coeff_map, MvPolynomial.coeff_C_mul, ih]
    simp only [Finsupp.cons_tail, Fin.prod_univ_succ, Finsupp.tail_apply]

end LeanCanny.Algebra.SeparateVariableCoefficients

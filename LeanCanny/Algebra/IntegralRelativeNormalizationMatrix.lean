/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralRelativeLeadingNormalization
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Actual multiplication matrices of normalized relative coefficients

The normalized top coefficient is an integer scalar. Every other
coefficient uses the matrix polynomial for the characteristic inverse of
the original top-coefficient matrix. This remains valid for finite
algebras with zero divisors; no inverse matrix or field embedding is used.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralRelativeNormalizationMatrix
open Polynomial IntegralRelativeLeadingNormalization
open scoped Classical BigOperators
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

noncomputable def top (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :=
  Algebra.leftMulMatrix b (p.coeff d)

noncomputable def inverseMatrix (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :=
  Polynomial.aeval (top b p d) (IntegralParameterInverse.inverse (top b p d).charpoly)

theorem inverseMatrix_eq (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    inverseMatrix b p d = Algebra.leftMulMatrix b (inverseValue b (p.coeff d)) := by
  unfold inverseMatrix top inverseValue
  rw [← Polynomial.aeval_algHom_apply]

theorem coefficient_eq (b : Module.Basis ι ℤ A) (p : Polynomial A) (d k : ℕ) :
    (normalize b p d).coeff k =
      if k = d then (denominator b (p.coeff d) : A)
      else inverseValue b (p.coeff d) * p.coeff k := by
  by_cases H : k = d
  · subst k
    rw [ite_eq_left rfl, coefficient]
  · have H' : d ≠ k := Ne.symm H
    simp only [IntegralRelativeLeadingNormalization.normalize, coeff_add, coeff_monomial, H', ite_false,
      coeff_C_mul, coeff_sub, sub_zero, zero_add, ite_eq_right H]

theorem matrix_eq (b : Module.Basis ι ℤ A) (p : Polynomial A) (d k : ℕ) :
    Algebra.leftMulMatrix b ((normalize b p d).coeff k) =
      if k = d then (denominator b (p.coeff d) : ℤ) • (1 : Matrix ι ι ℤ)
      else inverseMatrix b p d * Algebra.leftMulMatrix b (p.coeff k) := by
  rw [coefficient_eq]
  split_ifs with H
  · change (Algebra.leftMulMatrix b) (algebraMap ℤ A _) = _
    rw [AlgHom.commutes]
    simp only [Algebra.algebraMap_eq_smul_one]
  · rw [map_mul, ← inverseMatrix_eq]

theorem inverse_degree (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    (IntegralParameterInverse.inverse (top b p d).charpoly).natDegree ≤ Fintype.card ι := by
  exact (IntegralParameterInverse.natDegree_inverse_le _).trans (by rw [Matrix.charpoly_natDegree_eq_dim])

theorem inverseMatrix_sum (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    inverseMatrix b p d =
      ∑ j ∈ Finset.range (Fintype.card ι + 1),
        (IntegralParameterInverse.inverse (top b p d).charpoly).coeff j • top b p d ^ j := by
  unfold inverseMatrix
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le (inverse_degree b p d))]

theorem denominator_eq (b : Module.Basis ι ℤ A) (p : Polynomial A) (d : ℕ) :
    denominator b (p.coeff d) = IntegralParameterInverse.denominator (top b p d).charpoly := rfl

end LeanCanny.Algebra.IntegralRelativeNormalizationMatrix

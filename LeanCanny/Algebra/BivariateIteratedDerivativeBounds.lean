/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BivariateIteratedDerivativeSpace
public import LeanCanny.Algebra.CoefficientMass

/-! # Uniform bounds for binary-indexed bivariate derivatives

Outer differentiation does not increase parameter degree. Its coefficient
mass allowance depends only on the original outer degree and mass bound:
orders exceeding that degree contribute zero coefficients.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedPolynomial.BivariateIteratedDerivative
open Polynomial

theorem parameter_degree (p : (ℤ[X])[X]) (P : ℕ) (hp : ∀ i, (p.coeff i).natDegree ≤ P) (k i : ℕ) :
    ((Polynomial.derivative^[k] p).coeff i).natDegree ≤ P := by
  rw [Polynomial.coeff_iterate_derivative]
  exact (Polynomial.natDegree_smul_le _ _).trans (hp _)

private theorem nsmul_mass_le (n : ℕ) (p : ℤ[X]) : coefficientMass (n • p) ≤ n * coefficientMass p := by
  rw [nsmul_eq_mul, ← Polynomial.C_eq_natCast]
  simpa only [coefficientMass_C, Int.natAbs_natCast] using coefficientMass_mul_le (Polynomial.C (n : ℤ)) p

theorem coefficient_mass (p : (ℤ[X])[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ B) (k i : ℕ) :
    coefficientMass ((Polynomial.derivative^[k] p).coeff i) ≤ 2 ^ (B + D.size * D) := by
  rw [Polynomial.coeff_iterate_derivative]
  by_cases hi : i + k ≤ D
  · have hk : k ≤ D := by omega
    have hf : (i + k).descFactorial k ≤ 2 ^ (D.size * D) := by
      calc
        _ ≤ (i + k) ^ k := Nat.descFactorial_le_pow _ _
        _ ≤ D ^ k := Nat.pow_le_pow_left hi _
        _ ≤ (2 ^ D.size) ^ k := Nat.pow_le_pow_left (Nat.lt_size_self D).le _
        _ = 2 ^ (D.size * k) := (pow_mul _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hk)
    exact (nsmul_mass_le _ _).trans ((Nat.mul_le_mul hf (hB _)).trans_eq
      (by rw [← pow_add, Nat.add_comm]))
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]
    simp only [coefficientMass, Polynomial.sum_zero_index, Nat.zero_le]

theorem coefficient_mass_budget (p : (ℤ[X])[X]) (D B : ℕ) (hD : p.natDegree ≤ D)
    (hB : ∀ i, coefficientMass (p.coeff i) ≤ 2 ^ B) (k i : ℕ) :
    coefficientMass ((Polynomial.derivative^[k] p).coeff i) ≤ 2 ^ IteratedDerivativeBits.massBudget D B :=
  (coefficient_mass p D B hD hB k i).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))

end LeanCanny.Algebra.CertifiedPolynomial.BivariateIteratedDerivative

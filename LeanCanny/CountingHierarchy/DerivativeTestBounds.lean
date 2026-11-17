/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DerivativeProductBounds
public import LeanCanny.CountingHierarchy.AlgebraicTestValueBounds

/-! # Uniform degree, mass and value bounds for binary-indexed derivative tests -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial LeanCanny.Algebra

@[expose] def derivativeTestMassExponent (D b : ℕ) : ℕ := b + D.size * D

theorem iterated_derivative_mass_le (p : Polynomial ℤ) (D b : ℕ)
    (hD : p.natDegree ≤ D) (hb : coefficientMass p ≤ 2 ^ b) (k : ℕ) :
    coefficientMass (Polynomial.derivative^[k] p) ≤ 2 ^ derivativeTestMassExponent D b := by
  have hiter (j : ℕ) : coefficientMass (Polynomial.derivative^[j] p) ≤ D ^ j * coefficientMass p := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', pow_succ']
      apply (coefficientMass_derivative_le _).trans
      have hdeg := (Polynomial.natDegree_iterate_derivative p j).trans ((Nat.sub_le _ _).trans hD)
      exact (Nat.mul_le_mul hdeg ih).trans_eq (Nat.mul_assoc _ _ _).symm
  by_cases hk : k ≤ D
  · apply (hiter k).trans
    apply (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.lt_size_self D).le k) hb).trans
    rw [← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by
      have := Nat.mul_le_mul_left D.size hk
      dsimp only [derivativeTestMassExponent]
      omega)
  · rw [Polynomial.iterate_derivative_eq_zero (by omega), coefficientMass_zero]
    exact Nat.zero_le _

/-- A single effective precision works for all derivative orders, including
 orders above the actual degree and zero derivatives. -/
theorem iterated_derivative_value_range (p : Polynomial ℤ) (hp : p ≠ 0)
    (D b : ℕ) (hD : p.natDegree ≤ D) (hb : coefficientMass p ≤ 2 ^ b)
    (a : ℝ) (ha : p.eval₂ (Int.castRingHom ℝ) a = 0) (k : ℕ) :
    (Polynomial.derivative^[k] p).eval₂ (Int.castRingHom ℝ) a = 0 ∨
      (((2 : ℝ) ^ algebraicTestPrecision D D b (derivativeTestMassExponent D b))⁻¹ ≤
          |(Polynomial.derivative^[k] p).eval₂ (Int.castRingHom ℝ) a| ∧
        |(Polynomial.derivative^[k] p).eval₂ (Int.castRingHom ℝ) a| ≤
          (2 : ℝ) ^ algebraicTestPrecision D D b (derivativeTestMassExponent D b)) :=
  algebraic_test_value_range p _ hp D D b (derivativeTestMassExponent D b) hD
    ((Polynomial.natDegree_iterate_derivative p k).trans ((Nat.sub_le _ _).trans hD)) hb
    (iterated_derivative_mass_le p D b hD hb k) a ha

end LeanCanny.CountingHierarchy

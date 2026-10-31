/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionCoefficientMap
public import LeanCanny.Algebra.PartialDerivativeDegree

/-! # Derivatives under additive coefficient extraction

An old multiplication-matrix entry is additive. Its coefficient polynomial
has no larger spatial degree, and differentiation commutes with this
additive extraction. The statements require no multiplicativity or
preservation of one by the coefficient map.
-/

@[expose] public section
namespace LeanCanny.Algebra.PurePowerReductionBits
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] {n : ℕ}

theorem coefficientPolynomial_support (f : R →+ ℤ) (p : MvPolynomial (Fin n) R) :
    (coefficientPolynomial f p).support ⊆ p.support := by
  intro e he
  rw [mem_support_iff] at he ⊢
  intro h
  exact he (by rw [coefficientPolynomial_coeff, h, map_zero])

theorem coefficientPolynomial_degree (f : R →+ ℤ) (p : MvPolynomial (Fin n) R) :
    (coefficientPolynomial f p).totalDegree ≤ p.totalDegree := by
  unfold MvPolynomial.totalDegree
  exact Finset.sup_mono (coefficientPolynomial_support f p)

theorem coefficientPolynomial_pderiv (f : R →+ ℤ) (p : MvPolynomial (Fin n) R) (i : Fin n) :
    coefficientPolynomial f (pderiv i p) = pderiv i (coefficientPolynomial f p) := by
  apply MvPolynomial.ext
  intro e
  rw [coefficientPolynomial_coeff, coeff_pderiv, coeff_pderiv, coefficientPolynomial_coeff]
  have H : p.coeff (e + Finsupp.single i 1) * ((e i + 1 : ℕ) : R) =
      (e i + 1) • p.coeff (e + Finsupp.single i 1) := by
    rw [nsmul_eq_mul, mul_comm]
  simp only [Nat.cast_add, Nat.cast_one] at H
  rw [H, map_nsmul, nsmul_eq_mul]
  simp only [Nat.cast_add, Nat.cast_one, mul_comm]

end LeanCanny.Algebra.PurePowerReductionBits

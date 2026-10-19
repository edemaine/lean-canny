/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitution

/-!
# Rational substitution under coefficient reduction

Modular reduction can lower a source polynomial's variable degrees. The
denominator exponents must therefore retain the original degree allowances.
`clearedWith` makes those allowances explicit and commutes with every coefficient
ring map, including maps that kill coefficients. Recomputing degrees after
reduction is not required by this interface.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Polynomial
open scoped BigOperators

variable {σ R S : Type*} [Fintype σ] [CommSemiring R] [CommSemiring S]

noncomputable def clearedWith (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X]) : R[X] :=
  ∑ e ∈ p.support, C (p.coeff e) * ∏ i, n i ^ e i * d i ^ (2 * D i - e i)

theorem cleared_eq_clearedWith (p : MvPolynomial σ R) (n d : σ → R[X]) :
    cleared p n d = clearedWith p.degreeOf p n d := rfl

theorem map_clearedWith (φ : R →+* S) (D : σ → ℕ) (p : MvPolynomial σ R) (n d : σ → R[X]) :
    (clearedWith D p n d).map φ =
      clearedWith D (MvPolynomial.map φ p) (fun i => (n i).map φ) (fun i => (d i).map φ) := by
  classical
  simp only [clearedWith, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_prod,
    Polynomial.map_pow, Polynomial.map_C, MvPolynomial.coeff_map]
  symm
  apply Finset.sum_subset (MvPolynomial.support_map_subset φ p)
  intro e _ he
  have hc := MvPolynomial.notMem_support_iff.mp he
  rw [MvPolynomial.coeff_map] at hc
  simp only [hc, Polynomial.C_0, zero_mul]

theorem map_cleared (φ : R →+* S) (p : MvPolynomial σ R) (n d : σ → R[X]) :
    (cleared p n d).map φ =
      clearedWith p.degreeOf (MvPolynomial.map φ p) (fun i => (n i).map φ) (fun i => (d i).map φ) := by
  rw [cleared_eq_clearedWith, map_clearedWith]

theorem coeff_map_cleared (φ : R →+* S) (p : MvPolynomial σ R) (n d : σ → R[X]) (k : ℕ) :
    φ ((cleared p n d).coeff k) =
      (clearedWith p.degreeOf (MvPolynomial.map φ p) (fun i => (n i).map φ) (fun i => (d i).map φ)).coeff k := by
  rw [← map_cleared, Polynomial.coeff_map]

end LeanCanny.Algebra.RationalSubstitution

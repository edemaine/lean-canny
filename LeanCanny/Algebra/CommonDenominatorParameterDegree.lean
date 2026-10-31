/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonDenominatorSpecialization
public import LeanCanny.Algebra.PolynomialCoefficientDegree

/-! # Parameter degree under integral common-denominator substitution

A denominator constant in the retained parameter contributes no parameter
degree. Numerators of coefficient degree E increase the bound by at most
the original spatial degree times E.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonDenominatorSpecialization
open MvPolynomial
open scoped Classical BigOperators
variable {σ τ R : Type*} [Fintype σ] [CommRing R]

theorem parameter_degree (D : ℕ) (q : R) (v : σ → MvPolynomial τ (Polynomial R))
    (p : MvPolynomial σ (Polynomial R)) (S E : ℕ) (hp : PolynomialCoefficientDegree.Bound p S)
    (hv : ∀ i, PolynomialCoefficientDegree.Bound (v i) E) :
    PolynomialCoefficientDegree.Bound (clear D (Polynomial.C q) v p) (S + p.totalDegree * E) := by
  change PolynomialCoefficientDegree.Bound
    (∑ e ∈ p.support, C (p.coeff e) * factor D (Polynomial.C q) v e) _
  apply PolynomialCoefficientDegree.sum
  intro e he
  have HQ : PolynomialCoefficientDegree.Bound
      (C ((Polynomial.C q) ^ (D - e.degree)) : MvPolynomial τ (Polynomial R)) 0 := by
    apply PolynomialCoefficientDegree.C
    rw [← Polynomial.C_pow, Polynomial.natDegree_C]
  have HV := PolynomialCoefficientDegree.prod Finset.univ (fun i => v i ^ e i)
    (fun i => e i * E) (fun i _ => PolynomialCoefficientDegree.pow (hv i) (e i))
  have HF : PolynomialCoefficientDegree.Bound (factor D (Polynomial.C q) v e) (e.degree * E) := by
    simpa only [factor, Nat.zero_add, ← Finset.sum_mul, ← Finsupp.degree_eq_sum] using
      PolynomialCoefficientDegree.mul HQ HV
  exact PolynomialCoefficientDegree.mono (PolynomialCoefficientDegree.mul (PolynomialCoefficientDegree.C (hp e)) HF)
    (Nat.add_le_add_left (Nat.mul_le_mul_right E (MvPolynomial.le_totalDegree he)) S)

end LeanCanny.Algebra.CommonDenominatorSpecialization

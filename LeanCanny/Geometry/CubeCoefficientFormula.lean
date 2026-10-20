/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CubePolynomial
public import LeanCanny.Algebra.SeparateVariableCoefficients
public import LeanCanny.Algebra.CubeFactorCoefficients
public import LeanCanny.ETR.CollectedCoefficients

/-! # Compactified coefficients as indexed sums of binomial products

Clearing fixed coordinate denominator powers is additive in the source
polynomial. Hence the actual compactified coefficient can be read from the
indexed syntax expansion even when some indexed monomials cancel. Each
coordinate contributes the coefficient of one univariate cube factor.
-/

@[expose] public section

namespace LeanCanny.Geometry.CubePolynomial
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

noncomputable def clearHom (D : ι → ℕ) : MvPolynomial ι R →+ MvPolynomial ι R where
  toFun p := ∑ e ∈ p.support, C (p.coeff e) * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)
  map_zero' := by simp
  map_add' p q := by
    classical
    change Finsupp.sum (AddMonoidAlgebra.coeff (p + q)) (fun e a => C a * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)) =
      Finsupp.sum (AddMonoidAlgebra.coeff p) (fun e a => C a * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)) +
      Finsupp.sum (AddMonoidAlgebra.coeff q) (fun e a => C a * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i))
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.sum_add_index (fun _ _ => by simp) (fun _ _ _ _ => by simp only [map_add, add_mul])

theorem clearHom_monomial (D : ι → ℕ) (e : ι →₀ ℕ) (a : R) :
    clearHom D (monomial e a) = C a * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i) := by
  change Finsupp.sum (Finsupp.single e a) (fun e a => C a * ∏ i, X i ^ e i * (1 - X i ^ 2) ^ (2 * D i - e i)) = _
  exact Finsupp.sum_single_index (by simp)

theorem clearHom_eq_cleared (p : MvPolynomial ι ℤ) : clearHom p.degreeOf p = cleared p := rfl

theorem coeff_separate_cube_factors (A : ℕ) (e s : Fin A → ℕ) (k : Fin A →₀ ℕ) :
    (∏ i, (X i : MvPolynomial (Fin A) R) ^ e i * (1 - X i ^ 2) ^ s i).coeff k =
      ∏ i, (Algebra.CubeFactor.polynomial (R := R) (e i) (s i)).coeff (k i) := by
  have h : (∏ i, (X i : MvPolynomial (Fin A) R) ^ e i * (1 - X i ^ 2) ^ s i) =
      ∏ i, Polynomial.aeval (X i : MvPolynomial (Fin A) R) (Algebra.CubeFactor.polynomial (R := R) (e i) (s i)) := by
    simp only [Algebra.CubeFactor.polynomial, map_mul, map_pow, map_sub, map_one, Polynomial.aeval_X]
  rw [h]
  exact Algebra.SeparateVariableCoefficients.coeff_prod A _ k

theorem coeff_clearHom_source (A M : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ) (D : Fin A → ℕ) (k : ℕ → ℕ) :
    (clearHom D (Algebra.RationalSubstitution.Indexed.source A M a e)).coeff
      (Algebra.RationalSubstitution.Indexed.exponentVector A k) =
        ∑ r ∈ Finset.range M, a r * ∏ i : Fin A,
          (Algebra.CubeFactor.polynomial (R := R) (e r i) (2 * D i - e r i)).coeff (k i) := by
  classical
  rw [Algebra.RationalSubstitution.Indexed.source, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [clearHom_monomial, MvPolynomial.coeff_C_mul, coeff_separate_cube_factors]
  simp only [Algebra.RationalSubstitution.Indexed.exponentVector, Finsupp.coe_equivFunOnFinite_symm]

theorem coeff_cleared_finitePolynomial (t : ETR.Term) (A : ℕ) (hA : t.arity ≤ A) (k : ℕ → ℕ) :
    (cleared (ETR.Term.finitePolynomial A t)).coeff (Algebra.RationalSubstitution.Indexed.exponentVector A k) =
      ∑ r ∈ Finset.range t.monomialCount, t.monomialCoefficient r * ∏ i : Fin A,
        (Algebra.CubeFactor.polynomial (R := ℤ) (t.monomialExponent r i)
          (2 * (ETR.Term.finitePolynomial A t).degreeOf i - t.monomialExponent r i)).coeff (k i) := by
  have h := coeff_clearHom_source A t.monomialCount t.monomialCoefficient t.monomialExponent
    (ETR.Term.finitePolynomial A t).degreeOf k
  rw [← ETR.Term.finitePolynomial_eq_indexed_source t A hA, clearHom_eq_cleared] at h
  exact h

end LeanCanny.Geometry.CubePolynomial

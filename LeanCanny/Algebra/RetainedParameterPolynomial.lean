/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedMultivariateRational
public import LeanCanny.Algebra.IntegerParameterFlatten

/-! # Coefficients and derivatives of a retained parameter equation

A univariate equation is embedded in variable zero. Every spatial partial
vanishes, while the parameter partial is its ordinary derivative. The
coefficient mask explicitly excludes monomials using any spatial variable.
-/

@[expose] public section
namespace LeanCanny.Algebra.RetainedParameterPolynomial
open MvPolynomial
open scoped Classical
variable {n : ℕ}

theorem coefficient (p : Polynomial ℤ) (m : Fin (n + 1) →₀ ℕ) :
    (IndexedMultivariateRational.parameter n p).coeff m =
      if ∀ i : Fin n, m i.succ = 0 then p.coeff (m 0) else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, Polynomial.coeff_add]
    split_ifs <;> simp
  | monomial k a =>
    have he : (Finsupp.single (0 : Fin (n + 1)) k : Fin (n + 1) →₀ ℕ) = m ↔
        m 0 = k ∧ ∀ i : Fin n, m i.succ = 0 := by
      constructor
      · intro h
        rw [← h]
        simp
      · rintro ⟨h0, hs⟩
        ext j
        refine Fin.cases ?_ (fun i => ?_) j
        · simpa only [Finsupp.single_eq_same] using h0.symm
        · simp only [Finsupp.single_eq_of_ne (by simp : i.succ ≠ 0), hs]
    simp only [IndexedMultivariateRational.parameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      C_mul_X_pow_eq_monomial, coeff_monomial, Polynomial.coeff_monomial, he]
    by_cases hs : ∀ i : Fin n, m i.succ = 0
    · simp [hs, eq_comm]
    · simp only [hs, and_false, ite_false]

theorem spatial_partial (p : Polynomial ℤ) (i : Fin n) :
    pderiv i.succ (IndexedMultivariateRational.parameter n p) = 0 :=
  IntegerParameterFlatten.pderiv_coefficientMap p i

theorem parameter_partial (p : Polynomial ℤ) :
    pderiv (0 : Fin (n + 1)) (IndexedMultivariateRational.parameter n p) =
      IndexedMultivariateRational.parameter n p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial k a =>
    simp only [IndexedMultivariateRational.parameter, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.derivative_monomial, pderiv_mul, pderiv_C, zero_mul, zero_add, pderiv_pow, pderiv_X_self,
      mul_one, map_mul, map_natCast]
    ring

theorem mass (p : Polynomial ℤ) :
    MvMass.mass (IndexedMultivariateRational.parameter n p) ≤ coefficientMass p :=
  IntegerParameterFlatten.coefficientMap_mass p

end LeanCanny.Algebra.RetainedParameterPolynomial

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.InfinitesimalSign
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.FieldTheory.RatFunc.Basic

/-! # Lowest terms of polynomial quotients

For nonzero numerator and denominator, the order difference and the ratio of
trailing coefficients depend only on the rational function. Factoring the
lowest powers of X leaves polynomials with nonzero constant coefficients.
If the quotient is a polynomial, these data are its ordinary lowest term.
No polynomial divisibility is assumed in the rational construction.
-/

@[expose] public section

namespace LeanCanny.Algebra.PolynomialQuotientLowest
variable {R : Type*} [CommRing R] [IsDomain R]

noncomputable def quotient (p q : Polynomial R) : RatFunc R := RatFunc.mk p q

def order (p q : Polynomial R) : ℤ := (p.natTrailingDegree : ℤ) - q.natTrailingDegree

noncomputable def coefficient (p q : Polynomial R) : FractionRing R :=
  algebraMap R (FractionRing R) p.trailingCoeff / algebraMap R (FractionRing R) q.trailingCoeff

theorem cross_multiply {p q p' q' : Polynomial R} (hq : q ≠ 0) (hq' : q' ≠ 0)
    (h : quotient p q = quotient p' q') : p * q' = p' * q := by
  apply RatFunc.algebraMap_injective R
  rw [map_mul, map_mul]
  exact (div_eq_div_iff (RatFunc.algebraMap_ne_zero hq) (RatFunc.algebraMap_ne_zero hq')).mp
    (by simpa only [quotient, RatFunc.mk_eq_div] using h)

theorem invariant {p q p' q' : Polynomial R} (hp : p ≠ 0) (hq : q ≠ 0) (hp' : p' ≠ 0) (hq' : q' ≠ 0)
    (h : quotient p q = quotient p' q') : order p q = order p' q' ∧ coefficient p q = coefficient p' q' := by
  have hc := cross_multiply hq hq' h
  have hd := congrArg Polynomial.natTrailingDegree hc
  rw [Polynomial.natTrailingDegree_mul hp hq', Polynomial.natTrailingDegree_mul hp' hq] at hd
  have ht := congrArg Polynomial.trailingCoeff hc
  rw [Polynomial.trailingCoeff_mul, Polynomial.trailingCoeff_mul] at ht
  refine ⟨by unfold order; omega, ?_⟩
  have hn : algebraMap R (FractionRing R) q.trailingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq)
  have hn' : algebraMap R (FractionRing R) q'.trailingCoeff ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr
      (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq')
  apply (div_eq_div_iff hn hn').mpr
  simpa only [map_mul] using congrArg (algebraMap R (FractionRing R)) ht

theorem normalized (p q : Polynomial R) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a b : Polynomial R, p = Polynomial.X ^ p.natTrailingDegree * a ∧
      q = Polynomial.X ^ q.natTrailingDegree * b ∧ a.coeff 0 = p.trailingCoeff ∧ b.coeff 0 = q.trailingCoeff ∧
      a.coeff 0 ≠ 0 ∧ b.coeff 0 ≠ 0 ∧
      quotient p q = (algebraMap (Polynomial R) (RatFunc R) Polynomial.X) ^ order p q * quotient a b := by
  obtain ⟨a, ha, ha0⟩ := InfinitesimalSign.factor_at_trailingDegree p
  obtain ⟨b, hb, hb0⟩ := InfinitesimalSign.factor_at_trailingDegree q
  refine ⟨a, b, ha, hb, ha0, hb0, ?_, ?_, ?_⟩
  · rw [ha0]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  · rw [hb0]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hq
  · have hX : algebraMap (Polynomial R) (RatFunc R) Polynomial.X ≠ 0 :=
      RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
    simp only [quotient, RatFunc.mk_eq_div, order, zpow_sub₀ hX, zpow_natCast]
    conv_lhs => rw [ha, hb]
    rw [map_mul, map_mul, map_pow, map_pow]
    exact (div_mul_div_comm _ _ _ _).symm

theorem of_polynomial {p q r : Polynomial R} (hq : q ≠ 0) (hr : r ≠ 0) (h : p = r * q) :
    order p q = r.natTrailingDegree ∧
      coefficient p q = algebraMap R (FractionRing R) r.trailingCoeff := by
  have hp : p ≠ 0 := h ▸ mul_ne_zero hr hq
  have he : quotient p q = quotient r 1 := by
    rw [quotient, quotient, RatFunc.mk_eq_div, RatFunc.mk_eq_div, h, map_mul, map_one, div_one]
    exact mul_div_cancel_right₀ _ (RatFunc.algebraMap_ne_zero hq)
  have hi := invariant hp hq hr one_ne_zero he
  simpa [order, coefficient, Polynomial.trailingCoeff] using hi

end LeanCanny.Algebra.PolynomialQuotientLowest

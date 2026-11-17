/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.BigOperators

/-! # A nonvanishing power substitution for monic bivariate polynomials -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Polynomial

variable {R : Type*} [CommRing R]

/-- In `Q(U,T)`, substitute `U=V^(D+1)` and `T=V`. -/
noncomputable def monicPowerSubstitution (D : ℕ) (Q : Polynomial (Polynomial R)) : Polynomial R :=
  Q.eval₂ (Polynomial.expand R (D + 1)).toRingHom Polynomial.X

/-- Lower powers of `T` cannot contribute to the coefficient of `V^D`,
regardless of the degrees of their coefficients in `U`. -/
theorem monicPowerSubstitution_coeff (D : ℕ) (Q : Polynomial (Polynomial R))
    (hD : Q.natDegree ≤ D) (hc : Q.coeff D = 1) : (monicPowerSubstitution D Q).coeff D = 1 := by
  classical
  conv_lhs => rw [monicPowerSubstitution, Q.as_sum_range' (D + 1) (by omega)]
  rw [Polynomial.eval₂_finsetSum, Polynomial.finsetSum_coeff]
  simp only [Polynomial.eval₂_monomial]
  rw [Finset.sum_eq_single D]
  · simp only [hc, map_one, one_mul, Polynomial.coeff_X_pow, ite_true]
  · intro i hi hne
    have hiD : i < D := by have := Finset.mem_range.mp hi; omega
    have hsub : 0 < D - i := by omega
    have hlt : D - i < D + 1 := by omega
    rw [Polynomial.coeff_mul_X_pow', ite_eq_left hiD.le]
    change (Polynomial.expand R (D + 1) (Q.coeff i)).coeff (D - i) = 0
    rw [Polynomial.coeff_expand (by omega : 0 < D + 1),
      ite_eq_right (Nat.not_dvd_of_pos_of_lt hsub hlt)]
  · simp

theorem monicPowerSubstitution_monic_coeff (D : ℕ) (Q : Polynomial (Polynomial R))
    (hQ : Q.Monic) (hD : Q.natDegree = D) : (monicPowerSubstitution D Q).coeff D = 1 :=
  monicPowerSubstitution_coeff D Q hD.le (hD ▸ hQ.coeff_natDegree)

theorem monicPowerSubstitution_ne_zero [Nontrivial R] (D : ℕ) (Q : Polynomial (Polynomial R))
    (hQ : Q.Monic) (hD : Q.natDegree = D) : monicPowerSubstitution D Q ≠ 0 := by
  intro he
  have hc := monicPowerSubstitution_monic_coeff D Q hQ hD
  rw [he, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc

end LeanCanny.CountingHierarchy

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Ring

/-! # Binomial coefficients of compactification factors

The coefficient of `X^e (1-X²)^s` is zero unless the selected degree is
at least e and differs from e by an even number. Otherwise it is one signed
binomial coefficient. The formula covers all exponents, including truncation
of the denominator allowance when an indexed source term later cancels.
-/

@[expose] public section

namespace LeanCanny.Algebra.CubeFactor
open Polynomial

variable {R : Type*} [CommRing R]

noncomputable def polynomial (e s : ℕ) : Polynomial R := X ^ e * (1 - X ^ 2) ^ s

theorem coeff_one_sub_X_pow (s k : ℕ) : ((1 - X : Polynomial R) ^ s).coeff k =
    (s.choose k : R) * (-1) ^ k := by
  have h : (X + 1 : Polynomial R).comp (C (-1) * X) = 1 - X := by simp; ring
  rw [← h, ← Polynomial.pow_comp, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_X_add_one_pow]

theorem coeff_one_sub_X_sq_pow (s k : ℕ) : ((1 - X ^ 2 : Polynomial R) ^ s).coeff k =
    if 2 ∣ k then (s.choose (k / 2) : R) * (-1) ^ (k / 2) else 0 := by
  have h : (1 - X ^ 2 : Polynomial R) = Polynomial.expand R 2 (1 - X) := by simp
  rw [h, ← map_pow, Polynomial.coeff_expand (by decide)]
  simp only [coeff_one_sub_X_pow]

theorem coeff (e s k : ℕ) : (polynomial (R := R) e s).coeff k =
    if e ≤ k ∧ 2 ∣ k - e then (s.choose ((k - e) / 2) : R) * (-1) ^ ((k - e) / 2) else 0 := by
  rw [polynomial, Polynomial.coeff_X_pow_mul', coeff_one_sub_X_sq_pow]
  split_ifs <;> simp_all

end LeanCanny.Algebra.CubeFactor

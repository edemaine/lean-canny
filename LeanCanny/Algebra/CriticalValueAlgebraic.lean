/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.TranscendentalDerivation

/-! # Critical values are algebraic over the coefficient field

The algebraic chain rule shows that every derivation kills a critical value.
In characteristic zero this forces the value to be algebraic, even when the
critical point is defined over a transcendental field extension.
-/

@[expose] public section

namespace LeanCanny.Algebra.CriticalValueAlgebraic
open MvPolynomial
open scoped BigOperators

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem eval_pderiv_mul_X [DecidableEq ι] (p : MvPolynomial ι K) (x : ι → L) (i j : ι) :
    aeval x (pderiv i (p * X j)) = x j * aeval x (pderiv i p) +
      if i = j then aeval x p else 0 := by
  classical
  rw [pderiv_mul, map_add, map_mul, map_mul, aeval_X]
  by_cases h : i = j <;> simp [pderiv_X, h, mul_comm]

variable [Fintype ι]

theorem chain_rule (δ : Derivation K L L) (p : MvPolynomial ι K) (x : ι → L) :
    δ (aeval x p) = ∑ i, aeval x (pderiv i p) * δ (x i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, aeval_X, δ.leibniz, smul_eq_mul, hp, eval_pderiv_mul_X,
      add_mul, Finset.sum_add_distrib]
    simp [mul_assoc, ← Finset.mul_sum, ite_mul, add_comm]

theorem algebraic_of_gradient_zero [CharZero K] (p : MvPolynomial ι K) (x : ι → L)
    (hx : ∀ i, aeval x (pderiv i p) = 0) : IsAlgebraic K (aeval x p) := by
  apply TranscendentalDerivation.algebraic_of_all_derivations_vanish
  intro δ
  rw [chain_rule]
  simp only [hx, zero_mul, Finset.sum_const_zero]

end LeanCanny.Algebra.CriticalValueAlgebraic

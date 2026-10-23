/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.FieldTheory.Perfect

/-! # Derivatives of algebraic elements remain algebraic

When a derivation preserves a characteristic-zero coefficient field, implicit
differentiation of the minimal polynomial expresses the derivative of an
algebraic element as a quotient of polynomial values at that element.
-/

@[expose] public section

namespace LeanCanny.Algebra.AlgebraicDerivative
open Polynomial

variable {K B L : Type*} [Field K] [Field B] [Field L]
  [Algebra K B] [Algebra K L] [Algebra B L]

noncomputable def coefficientPolynomial (D : Derivation K B B) (p : Polynomial B) : Polynomial B :=
  PolynomialModule.equivPolynomial (D.mapCoeffs p)

theorem eval_map (x : L) (q : PolynomialModule B B) :
    PolynomialModule.eval x (PolynomialModule.map L (Algebra.linearMap B L) q) =
      Polynomial.aeval x (PolynomialModule.equivPolynomial q) := by
  exact (PolynomialModule.aeval_equivPolynomial q x).symm

theorem chain_rule (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b)) (x : L) (p : Polynomial B) :
    δ (Polynomial.aeval x p) = Polynomial.aeval x (coefficientPolynomial D p) +
      Polynomial.aeval x (derivative p) * δ x := by
  have h := Derivation.apply_aeval_eq' D δ (Algebra.linearMap B L) (fun b => (hD b).symm) x p
  rw [eval_map, smul_eq_mul] at h
  exact h

theorem algebraic_aeval {x : L} (hx : IsAlgebraic B x) (p : Polynomial B) :
    IsAlgebraic B (Polynomial.aeval x p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n b =>
    rw [Polynomial.aeval_monomial]
    exact (isAlgebraic_algebraMap b).mul (hx.pow n)

theorem algebraic_derivative [CharZero B] (D : Derivation K B B) (δ : Derivation K L L)
    (hD : ∀ b : B, δ (algebraMap B L b) = algebraMap B L (D b))
    {x : L} (hx : IsAlgebraic B x) : IsAlgebraic B (δ x) := by
  let p := minpoly B x
  have hp : Polynomial.aeval x p = 0 := minpoly.aeval B x
  have hsep : p.Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hx.isIntegral)
  have hne : Polynomial.aeval x (derivative p) ≠ 0 := hsep.aeval_derivative_ne_zero hp
  have hchain := chain_rule D δ hD x p
  rw [hp, map_zero] at hchain
  have hformula : δ x = -Polynomial.aeval x (coefficientPolynomial D p) / Polynomial.aeval x (derivative p) := by
    apply (eq_div_iff hne).mpr
    have hmul := eq_neg_of_add_eq_zero_right hchain.symm
    simpa only [mul_comm] using hmul
  rw [hformula, div_eq_mul_inv]
  exact (algebraic_aeval hx _).neg.mul (algebraic_aeval hx _).inv

end LeanCanny.Algebra.AlgebraicDerivative

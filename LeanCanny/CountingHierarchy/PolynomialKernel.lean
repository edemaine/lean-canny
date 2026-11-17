/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Tactic.Ring

/-!
# Polynomial reproducing kernels

A normalized polynomial kernel annihilating the coordinate differences
reproduces evaluation under a linear functional. The hypothesis is a
polynomial identity, with no assumptions about roots or characteristic.
-/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial

variable {A σ : Type*} [CommRing A]

theorem polynomial_kernel_reproduces (L : MvPolynomial σ A →ₗ[A] A)
    (K : MvPolynomial σ A) (x : σ → A) (hone : L K = 1)
    (hcoord : ∀ i q, L (K * q * (X i - C (x i))) = 0)
    (q : MvPolynomial σ A) : L (K * q) = eval x q := by
  have hscalar (a : A) (v : MvPolynomial σ A) : L (v * C a) = a * L v := by
    rw [mul_comm v, ← smul_eq_C_mul, map_smul, smul_eq_mul]
  induction q using MvPolynomial.induction_on with
  | C a => simp only [hscalar, hone, mul_one, eval_C]
  | add q r hq hr => simp only [mul_add, map_add, hq, hr]
  | mul_X q i hq =>
    have hz := hcoord i q
    rw [mul_sub, map_sub, sub_eq_zero] at hz
    rw [← mul_assoc, hz, hscalar, hq, map_mul, eval_X, mul_comm]

end LeanCanny.CountingHierarchy

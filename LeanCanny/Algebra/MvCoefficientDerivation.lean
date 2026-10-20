/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Coefficient derivations on multivariate polynomials

A derivation of the coefficient algebra acts coefficientwise, holding every
polynomial variable fixed. The number of variables need not be finite.
-/

@[expose] public section

namespace LeanCanny.Algebra.MvCoefficientDerivation
open MvPolynomial

variable {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]

noncomputable def linearMap (D : Derivation K A A) : MvPolynomial ι A →ₗ[K] MvPolynomial ι A :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap D.toLinearMap).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

theorem linearMap_monomial (D : Derivation K A A) (n : ι →₀ ℕ) (a : A) :
    linearMap D (monomial n a) = monomial n (D a) := by
  simp [linearMap, monomial]

theorem linearMap_mul (D : Derivation K A A) (p q : MvPolynomial ι A) :
    linearMap D (p * q) = p * linearMap D q + q * linearMap D p := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [add_mul, map_add, hp, hq, mul_add]; ring
  | monomial n a =>
    induction q using MvPolynomial.induction_on' with
    | add p q hp hq => simp only [mul_add, map_add, hp, hq, add_mul]; ring
    | monomial m b =>
      simp only [monomial_mul_monomial, linearMap_monomial, D.leibniz, smul_eq_mul,
        map_add, add_comm m n]

noncomputable def derivation (D : Derivation K A A) :
    Derivation K (MvPolynomial ι A) (MvPolynomial ι A) where
  toLinearMap := linearMap D
  map_one_eq_zero' := by
    change linearMap D (monomial 0 1) = 0
    rw [linearMap_monomial, D.map_one_eq_zero, monomial_zero]
  leibniz' p q := linearMap_mul D p q

theorem derivation_monomial (D : Derivation K A A) (n : ι →₀ ℕ) (a : A) :
    derivation D (monomial n a) = monomial n (D a) := linearMap_monomial D n a

theorem derivation_C (D : Derivation K A A) (a : A) : derivation D (C a : MvPolynomial ι A) = C (D a) :=
  derivation_monomial D 0 a

theorem derivation_X (D : Derivation K A A) (i : ι) : derivation D (X i) = 0 := by
  rw [X, derivation_monomial, D.map_one_eq_zero, monomial_zero]

end LeanCanny.Algebra.MvCoefficientDerivation

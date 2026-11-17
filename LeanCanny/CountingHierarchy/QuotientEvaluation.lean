/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientMultiplicationMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Evaluating quotient classes at common zeros of their relations -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical

variable {S : Type*} [CommRing S] {n ell : ℕ}

theorem aeval_mem_relation_ideal (r : Fin n → MvPolynomial (Fin n) S) (x : Fin n → S)
    (hx : ∀ i, MvPolynomial.aeval x (r i) = x i ^ ell)
    (q : MvPolynomial (Fin n) S) (hq : q ∈ relationIdeal ell r) :
    MvPolynomial.aeval x q = 0 := by
  have hker : relationIdeal ell r ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change MvPolynomial.aeval x (X i ^ ell - r i) = 0
    simp only [map_sub, map_pow, MvPolynomial.aeval_X, hx, sub_self]
  exact hker hq

/-- Evaluation at a common zero is an algebra hom on the actual quotient. -/
@[expose] noncomputable def quotientEvaluation
    (r : Fin n → MvPolynomial (Fin n) S) (x : Fin n → S)
    (hx : ∀ i, MvPolynomial.aeval x (r i) = x i ^ ell) :
    QuotientAlgebra ell r →ₐ[S] S :=
  Ideal.Quotient.liftₐ (relationIdeal ell r) (MvPolynomial.aeval x)
    (aeval_mem_relation_ideal r x hx)

@[simp] theorem quotientEvaluation_projection
    (r : Fin n → MvPolynomial (Fin n) S) (x : Fin n → S)
    (hx : ∀ i, MvPolynomial.aeval x (r i) = x i ^ ell)
    (q : MvPolynomial (Fin n) S) :
    quotientEvaluation r x hx (projection ell r q) = MvPolynomial.aeval x q := by
  exact congrArg (fun f : MvPolynomial (Fin n) S →ₐ[S] S => f q)
    (Ideal.Quotient.liftₐ_comp (relationIdeal ell r) (MvPolynomial.aeval x)
      (aeval_mem_relation_ideal r x hx))

/-- Cayley--Hamilton on the faithful regular representation gives the
 characteristic relation inside the quotient itself. -/
theorem aeval_charpoly_projection (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) :
    Polynomial.aeval (projection ell r v) (multiplicationMatrix hell r hr v).charpoly = 0 := by
  exact Algebra.aeval_charpoly_leftMulMatrix (normalBasis hell r hr) (projection ell r v)

/-- Every common zero gives a characteristic root, over any commutative
 coefficient ring. No spectral simplicity is needed for this direction. -/
theorem charpoly_eval_at_common_zero (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell)
    (v : MvPolynomial (Fin n) S) (x : Fin n → S)
    (hx : ∀ i, MvPolynomial.aeval x (r i) = x i ^ ell) :
    Polynomial.aeval (MvPolynomial.aeval x v) (multiplicationMatrix hell r hr v).charpoly = 0 := by
  rw [← quotientEvaluation_projection r x hx v, Polynomial.aeval_algHom_apply,
    aeval_charpoly_projection, map_zero]

end LeanCanny.CountingHierarchy.PurePowerResidue

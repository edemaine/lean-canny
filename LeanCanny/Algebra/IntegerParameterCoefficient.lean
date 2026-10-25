/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerParameterFlatten

/-! # Coefficients of the integer parameter representation

A coefficient query splits into the exponent of variable zero and the tail
of the spatial exponents. The coefficient is exactly one coefficient of the
original parameter polynomial, without any summation or expansion.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerParameterFlatten
open scoped Classical BigOperators
open MvPolynomial
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def tailExponent (a : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i.succ)

noncomputable def joinExponent (k : ℕ) (e : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.single 0 k + e.mapDomain Fin.succ

@[simp] theorem tailExponent_apply (a : Fin (n + 1) →₀ ℕ) (i : Fin n) :
    tailExponent a i = a i.succ := rfl

@[simp] theorem joinExponent_zero (k : ℕ) (e : Fin n →₀ ℕ) : joinExponent k e 0 = k := by
  have h : 0 ∉ Set.range (Fin.succ : Fin n → Fin (n + 1)) := by simp
  simp only [joinExponent, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.mapDomain_of_notMem_range e 0 h, Nat.add_zero]

@[simp] theorem joinExponent_succ (k : ℕ) (e : Fin n →₀ ℕ) (i : Fin n) :
    joinExponent k e i.succ = e i := by
  simp only [joinExponent, Finsupp.add_apply, Finsupp.single_eq_of_ne (Fin.succ_ne_zero i),
    Finsupp.mapDomain_apply_of_injective (Fin.succ_injective n), Nat.zero_add]

theorem joinExponent_eq_iff (k : ℕ) (e : Fin n →₀ ℕ) (a : Fin (n + 1) →₀ ℕ) :
    joinExponent k e = a ↔ k = a 0 ∧ e = tailExponent a := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [joinExponent_zero] using congrArg (fun b : Fin (n + 1) →₀ ℕ => b 0) h
    · ext i
      simpa only [joinExponent_succ, tailExponent_apply] using
        congrArg (fun b : Fin (n + 1) →₀ ℕ => b i.succ) h
  · rintro ⟨hk, he⟩
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [joinExponent_zero] using hk
    · simp only [joinExponent_succ, he, tailExponent_apply]

theorem flatten_monomial_monomial (e : Fin n →₀ ℕ) (k : ℕ) (c : R) :
    flatten (monomial e (Polynomial.monomial k c)) = monomial (joinExponent k e) c := by
  have hs : e.prod (fun i j => (X i.succ : MvPolynomial (Fin (n + 1)) R) ^ j) =
      rename Fin.succ (monomial e (1 : R)) := by
    simp only [MvPolynomial.monomial_eq, map_one, one_mul, map_finsuppProd,
      map_pow, rename_X]
  change (monomial e (Polynomial.monomial k c)).eval₂ coefficientMap (fun i => X i.succ) = _
  rw [eval₂_monomial, hs, rename_monomial]
  change Polynomial.eval₂ C (X 0) (Polynomial.monomial k c) * monomial (e.mapDomain Fin.succ) 1 = _
  rw [Polynomial.eval₂_monomial, C_mul_X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  rfl

/-- Splitting the native exponent reads precisely one original scalar
coefficient, including unsupported monomials and zero-dimensional systems. -/
theorem coeff_flatten (q : MvPolynomial (Fin n) (Polynomial R)) (a : Fin (n + 1) →₀ ℕ) :
    (flatten q).coeff a = (q.coeff (tailExponent a)).coeff (a 0) := by
  induction q using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp, hq]
  | monomial e c =>
    induction c using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, Polynomial.coeff_add, hp, hq]
    | monomial k c =>
      rw [flatten_monomial_monomial, coeff_monomial, coeff_monomial]
      by_cases he : e = tailExponent a <;> by_cases hk : k = a 0 <;>
        simp [joinExponent_eq_iff, he, hk, Polynomial.coeff_monomial]

end LeanCanny.Algebra.IntegerParameterFlatten

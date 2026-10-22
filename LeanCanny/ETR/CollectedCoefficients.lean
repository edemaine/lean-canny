/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomial
public import LeanCanny.ETR.IndexedExpansionBounds
public import Mathlib.Algebra.MvPolynomial.Funext

/-! # Collected polynomial coefficients from indexed expression terms

The indexed expansion may repeat exponent vectors. Summing exactly the terms
whose exponents match a requested vector gives the actual polynomial
coefficient, including cancellation and zero constants.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Algebra.RationalSubstitution.Indexed
open scoped BigOperators

theorem finitePolynomial_eq_indexed_source (t : Term) (A : ℕ) (hA : t.arity ≤ A) :
    finitePolynomial A t = source A t.monomialCount t.monomialCoefficient t.monomialExponent := by
  apply MvPolynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
  apply MvPolynomial.funext
  intro y
  simp only [MvPolynomial.eval_map]
  rw [eval_finitePolynomial]
  have h := eval₂_indexed_source (R := ℝ) t (Formula.extend y) A hA
  have he : (fun i : Fin A => Formula.extend y i.val) = y := by
    funext i
    simp [Formula.extend, i.isLt]
  rw [he] at h
  exact h.symm

theorem exponentVector_eq_iff (A : ℕ) (e f : ℕ → ℕ) :
    exponentVector A e = exponentVector A f ↔ ∀ i < A, e i = f i := by
  constructor
  · intro h i hi
    have he := congrArg (fun v : Fin A →₀ ℕ => v ⟨i, hi⟩) h
    simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm] using he
  · intro h
    ext i
    exact h i i.isLt

theorem finitePolynomial_coeff (t : Term) (A : ℕ) (hA : t.arity ≤ A) (e : ℕ → ℕ) :
    (finitePolynomial A t).coeff (exponentVector A e) =
      ∑ r ∈ Finset.range t.monomialCount,
        if ∀ i < A, t.monomialExponent r i = e i then t.monomialCoefficient r else 0 := by
  classical
  rw [finitePolynomial_eq_indexed_source t A hA, source, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [MvPolynomial.coeff_monomial, exponentVector_eq_iff]

theorem exponent_le_of_finitePolynomial_coeff_ne_zero (t : Term) (A : ℕ) (e : ℕ → ℕ)
    (hne : (finitePolynomial A t).coeff (exponentVector A e) ≠ 0) (i : ℕ) (hi : i < A) :
    e i ≤ t.degreeBound := by
  have hm := MvPolynomial.mem_support_iff.mpr hne
  have hd := (MvPolynomial.monomial_le_degreeOf (⟨i, hi⟩ : Fin A) hm).trans
    ((MvPolynomial.degreeOf_le_totalDegree _ _).trans (totalDegree_finitePolynomial t A))
  simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm] using hd

end LeanCanny.ETR.Term

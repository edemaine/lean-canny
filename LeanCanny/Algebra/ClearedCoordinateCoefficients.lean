/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateBlock
public import LeanCanny.Algebra.FixedWidthPolynomial

/-! # Explicit coefficients of denominator-cleared frozen substitutions

Each original spatial monomial contributes to exactly one free exponent.
Its algebra-valued coefficient is a product of the original coefficient,
the common denominator power, and frozen-height powers. A fixed-width
source grid therefore supplies the cleared coefficients without expanding
polynomials in the old scalar parameters.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateBlock
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n dim : ℕ} {R : Type*} [CommRing R]

noncomputable def exponentAtom (offset dim i e : ℕ) : Fin dim →₀ ℕ :=
  if hi : offset ≤ i ∧ i < offset + dim then Finsupp.single ⟨i - offset, by omega⟩ e else 0

def scalarAtom (q : R) (H : ℕ → R) (offset dim i e : ℕ) : R :=
  if offset ≤ i ∧ i < offset + dim then q ^ e else H i ^ e

noncomputable def freeExponent (offset dim : ℕ) (e : Fin n →₀ ℕ) : Fin dim →₀ ℕ :=
  ∑ i : Fin n, exponentAtom offset dim i.val (e i)

theorem freeExponent_apply (offset : ℕ) (hfit : offset + dim ≤ n) (e : Fin n →₀ ℕ) (j : Fin dim) :
    freeExponent offset dim e j = e ⟨offset + j.val, by omega⟩ := by
  let r : Fin n := ⟨offset + j.val, by omega⟩
  have hr : offset ≤ r.val ∧ r.val < offset + dim := by dsimp only [r]; omega
  rw [freeExponent, Finset.sum_apply', Finset.sum_eq_single r]
  · rw [exponentAtom, dite_eq_left hr, Finsupp.single_apply]
    have HJ : (⟨r.val - offset, by omega⟩ : Fin dim) = j := by
      apply Fin.ext
      dsimp only [r]
      omega
    rw [HJ, ite_eq_left rfl]
  · intro i _ hir
    by_cases hi : offset ≤ i.val ∧ i.val < offset + dim
    · rw [exponentAtom, dite_eq_left hi, Finsupp.single_apply]
      have HJ : (⟨i.val - offset, by omega⟩ : Fin dim) ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        apply hir
        apply Fin.ext
        dsimp only [r]
        dsimp only at hv
        omega
      rw [ite_eq_right HJ]
    · rw [exponentAtom, dite_eq_right hi, Finsupp.zero_apply]
  · intro h
    exact False.elim (h (Finset.mem_univ r))

noncomputable def monomialScalar (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (e : Fin n →₀ ℕ) (a : R) : R :=
  a * q ^ (D - e.degree) * ∏ i : Fin n, scalarAtom q H offset dim i.val (e i)

theorem coordinate_power (q : R) (H : ℕ → R) (offset dim i e : ℕ) :
    coordinate q H offset dim i ^ e = monomial (exponentAtom offset dim i e) (scalarAtom q H offset dim i e) := by
  by_cases hi : offset ≤ i ∧ i < offset + dim
  · simp only [coordinate, exponentAtom, scalarAtom, dite_eq_left hi, ite_eq_left hi,
      mul_pow, ← map_pow, X_pow_eq_monomial, C_mul_monomial, mul_one]
  · simp only [coordinate, exponentAtom, scalarAtom, dite_eq_right hi, ite_eq_right hi,
      ← map_pow, monomial_zero']

theorem monomial_product {ι : Type*} (s : Finset ι) (m : ι → Fin dim →₀ ℕ) (a : ι → R) :
    (∏ i ∈ s, monomial (m i) (a i)) = monomial (∑ i ∈ s, m i) (∏ i ∈ s, a i) := by
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, monomial_zero', map_one]
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons, Finset.prod_cons, ih, monomial_mul_monomial]

theorem specialize_monomial (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (e : Fin n →₀ ℕ) (a : R) :
    specialize D q H offset dim (monomial e a) =
      monomial (freeExponent offset dim e) (monomialScalar D q H offset dim e a) := by
  rw [specialize, CommonDenominatorSpecialization.monomial, CommonDenominatorSpecialization.factor]
  simp only [coordinate_power]
  rw [monomial_product, C_mul_monomial, C_mul_monomial]
  simp only [freeExponent, monomialScalar, mul_assoc]

theorem specialize_coefficient_grid (B : ℕ) (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (p : MvPolynomial (Fin n) R) (hp : ∀ e ∈ p.support, ∀ i, e i < 2 ^ B) (m : Fin dim →₀ ℕ) :
    (specialize D q H offset dim p).coeff m =
      ∑ r : Fin (FixedWidthPolynomial.count n B),
        if freeExponent offset dim (FixedWidthPolynomial.vector n B r) = m then
          monomialScalar D q H offset dim (FixedWidthPolynomial.vector n B r)
            (p.coeff (FixedWidthPolynomial.vector n B r)) else 0 := by
  have HS := FixedWidthPolynomial.sum_monomials_eq n B p hp
  conv_lhs => rw [← HS]
  rw [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [specialize_monomial, coeff_monomial]

end LeanCanny.Algebra.ClearedCoordinateBlock

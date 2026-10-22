/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficients

/-! # Actual variable degrees from surviving indexed monomials

An indexed exponent contributes only when the coefficient obtained by
collecting all equal monomials is nonzero. The maximum of these exponents
is the actual polynomial degree, including complete cancellation.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Algebra.RationalSubstitution.Indexed

noncomputable def survivingExponent (t : Term) (A r i : ℕ) : ℕ := by
  classical
  exact if (finitePolynomial A t).coeff (exponentVector A (t.monomialExponent r)) = 0 then 0 else t.monomialExponent r i

noncomputable def indexedDegree (t : Term) (A i : ℕ) : ℕ :=
  (Finset.range t.monomialCount).sup (fun r => survivingExponent t A r i)

theorem survivingExponent_le (t : Term) (A r i : ℕ) : survivingExponent t A r i ≤ t.degreeBound := by
  classical
  unfold survivingExponent
  split_ifs
  · exact Nat.zero_le _
  · exact t.monomialExponent_le r i

theorem indexedDegree_eq_degreeOf (t : Term) (A : ℕ) (hA : t.arity ≤ A) (i : Fin A) :
    indexedDegree t A i = (finitePolynomial A t).degreeOf i := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro r _
    unfold survivingExponent
    split_ifs with hz
    · exact Nat.zero_le _
    · have hd := MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hz)
      simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm] using hd
  · apply MvPolynomial.degreeOf_le_iff.mpr
    intro m hm
    let e : ℕ → ℕ := fun j => if hj : j < A then m ⟨j, hj⟩ else 0
    have he : exponentVector A e = m := by
      ext j
      simp only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, e, j.isLt, dite_true]
    have hc : (finitePolynomial A t).coeff (exponentVector A e) ≠ 0 := by
      rw [he]
      exact MvPolynomial.mem_support_iff.mp hm
    have hsum := finitePolynomial_coeff t A hA e
    have hn : (∑ r ∈ Finset.range t.monomialCount,
        if ∀ j < A, t.monomialExponent r j = e j then t.monomialCoefficient r else 0) ≠ 0 := by
      rw [← hsum]
      exact hc
    obtain ⟨r, hr, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hmatch : ∀ j < A, t.monomialExponent r j = e j := by
      by_contra h
      exact hterm (ite_eq_right h)
    have hv : exponentVector A (t.monomialExponent r) = m :=
      ((exponentVector_eq_iff _ _ _).mpr hmatch).trans he
    have hs : survivingExponent t A r i = m i := by
      rw [survivingExponent, hv, ite_eq_right (MvPolynomial.mem_support_iff.mp hm)]
      simpa only [e, i.isLt, dite_true] using hmatch i i.isLt
    rw [← hs]
    exact Finset.le_sup (f := fun r => survivingExponent t A r i) hr

theorem indexedDegree_eq_zero_of_arity_le (t : Term) (A i : ℕ) (hi : t.arity ≤ i) :
    indexedDegree t A i = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro r _
  simp only [survivingExponent, monomialExponent_eq_zero_of_arity_le t r i hi, ite_self, le_refl]

end LeanCanny.ETR.Term

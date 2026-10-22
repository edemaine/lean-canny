/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomialPadding
public import LeanCanny.ETR.CollectedCoefficients

/-! # Coefficients under padding by unused variables

An exponent vector with zeros in the extra coordinates is the injective
renaming of its original vector. The coefficient is therefore unchanged.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Algebra.RationalSubstitution.Indexed

theorem exponentVector_castLE (n N : ℕ) (hN : n ≤ N) (e : ℕ → ℕ)
    (he : ∀ i, n ≤ i → i < N → e i = 0) :
    (exponentVector n e).mapDomain (Fin.castLE hN) = exponentVector N e := by
  classical
  have hs : (↑(exponentVector N e).support : Set (Fin N)) ⊆ Set.range (Fin.castLE hN) := by
    intro i hi
    have hne : e i.val ≠ 0 := by
      simpa only [exponentVector, Finsupp.coe_equivFunOnFinite_symm] using Finsupp.mem_support_iff.mp hi
    have hin : i.val < n := by
      by_contra h
      exact hne (he i.val (Nat.le_of_not_gt h) i.isLt)
    exact ⟨⟨i.val, hin⟩, Fin.ext rfl⟩
  have hc : (exponentVector N e).comapDomain (Fin.castLE hN) (Fin.castLE_injective hN).injOn = exponentVector n e := by
    ext i
    simp only [Finsupp.comapDomain_apply, exponentVector, Finsupp.coe_equivFunOnFinite_symm, Fin.val_castLE]
  rw [← hc]
  exact Finsupp.mapDomain_comapDomain (Fin.castLE hN) (Fin.castLE_injective hN) _ hs

theorem coeff_finitePolynomial_padding (t : Term) (n N : ℕ) (hn : t.arity ≤ n) (hN : n ≤ N)
    (e : ℕ → ℕ) (he : ∀ i, n ≤ i → i < N → e i = 0) :
    (finitePolynomial N t).coeff (exponentVector N e) = (finitePolynomial n t).coeff (exponentVector n e) := by
  have h := MvPolynomial.coeff_rename_mapDomain (Fin.castLE hN) (Fin.castLE_injective hN) (finitePolynomial n t) (exponentVector n e)
  rw [rename_finitePolynomial t n N hn hN, exponentVector_castLE n N hN e he] at h
  exact h

end LeanCanny.ETR.Term

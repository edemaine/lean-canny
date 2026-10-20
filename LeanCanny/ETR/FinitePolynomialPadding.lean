/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # Padding finite source polynomials with unused variables

Once the dimension covers the syntax arity, larger dimensions only rename
the variables. Actual coordinate degrees are therefore unchanged by padding.
-/

@[expose] public section

namespace LeanCanny.ETR.Term

theorem rename_finitePolynomial (t : Term) (n N : ℕ) (hn : t.arity ≤ n) (hN : n ≤ N) :
    MvPolynomial.rename (Fin.castLE hN) (finitePolynomial n t) = finitePolynomial N t := by
  induction t with
  | const z => simp only [finitePolynomial, MvPolynomial.rename_C]
  | var i =>
    have hi : i < n := hn
    have hiN : i < N := hi.trans_le hN
    simp only [finitePolynomial, hi, hiN, dite_true, MvPolynomial.rename_X]
    rfl
  | add t u ht hu =>
    simp only [arity, max_le_iff] at hn
    simp only [finitePolynomial, map_add, ht hn.1, hu hn.2]
  | mul t u ht hu =>
    simp only [arity, max_le_iff] at hn
    simp only [finitePolynomial, map_mul, ht hn.1, hu hn.2]

theorem degreeOf_finitePolynomial_padding (t : Term) (n N : ℕ) (hn : t.arity ≤ n) (hN : n ≤ N) (i : Fin n) :
    (finitePolynomial N t).degreeOf (Fin.castLE hN i) = (finitePolynomial n t).degreeOf i := by
  rw [← rename_finitePolynomial t n N hn hN]
  exact MvPolynomial.degreeOf_rename_of_injective (Fin.castLE_injective hN) i

end LeanCanny.ETR.Term

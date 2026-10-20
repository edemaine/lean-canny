/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.FinitePolynomialPadding
public import LeanCanny.ETR.CollectedDegree
public import LeanCanny.Geometry.CubeCoefficientFormula

/-! # Compactified coefficients survive padding by unused variables

Extra variables have source degree zero. Their compactification factors are
one, so zero-padding the exponent query preserves each original coefficient.
-/

@[expose] public section

namespace LeanCanny.ETR.Term
open Algebra.RationalSubstitution.Indexed
open scoped BigOperators

noncomputable def cubeFactorCoefficient (t : Term) (A r : ℕ) (k : ℕ → ℕ) (i : ℕ) : ℤ :=
  (Algebra.CubeFactor.polynomial (R := ℤ) (t.monomialExponent r i)
    (2 * indexedDegree t A i - t.monomialExponent r i)).coeff (k i)

theorem coeff_cleared_eq_indexed_sum (t : Term) (A : ℕ) (hA : t.arity ≤ A) (k : ℕ → ℕ) :
    (Geometry.CubePolynomial.cleared (finitePolynomial A t)).coeff (exponentVector A k) =
      ∑ r ∈ Finset.range t.monomialCount, t.monomialCoefficient r *
        ∏ i ∈ Finset.range A, cubeFactorCoefficient t A r k i := by
  rw [Geometry.CubePolynomial.coeff_cleared_finitePolynomial t A hA k]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  rw [← Fin.prod_univ_eq_prod_range (cubeFactorCoefficient t A r k)]
  apply Finset.prod_congr rfl
  intro i _
  unfold cubeFactorCoefficient
  rw [indexedDegree_eq_degreeOf t A hA i]

theorem cubeFactorCoefficient_padding (t : Term) (n N : ℕ) (hn : t.arity ≤ n) (hN : n ≤ N)
    (r : ℕ) (k : ℕ → ℕ) (i : ℕ) (hi : i < n) :
    cubeFactorCoefficient t N r k i = cubeFactorCoefficient t n r k i := by
  unfold cubeFactorCoefficient
  rw [indexedDegree_eq_degreeOf t N (hn.trans hN) ⟨i, hi.trans_le hN⟩,
    indexedDegree_eq_degreeOf t n hn ⟨i, hi⟩]
  have hd := degreeOf_finitePolynomial_padding t n N hn hN ⟨i, hi⟩
  change (finitePolynomial N t).degreeOf ⟨i, hi.trans_le hN⟩ = (finitePolynomial n t).degreeOf ⟨i, hi⟩ at hd
  rw [hd]

theorem cubeFactorCoefficient_unused (t : Term) (A r : ℕ) (k : ℕ → ℕ) (i : ℕ)
    (hi : t.arity ≤ i) (hk : k i = 0) : cubeFactorCoefficient t A r k i = 1 := by
  rw [cubeFactorCoefficient, monomialExponent_eq_zero_of_arity_le t r i hi,
    indexedDegree_eq_zero_of_arity_le t A i hi, hk]
  simp [Algebra.CubeFactor.polynomial]

theorem coeff_cleared_padding (t : Term) (n N : ℕ) (hn : t.arity ≤ n) (hN : n ≤ N)
    (k : ℕ → ℕ) (hk : ∀ i, n ≤ i → i < N → k i = 0) :
    (Geometry.CubePolynomial.cleared (finitePolynomial N t)).coeff (exponentVector N k) =
      (Geometry.CubePolynomial.cleared (finitePolynomial n t)).coeff (exponentVector n k) := by
  rw [coeff_cleared_eq_indexed_sum t N (hn.trans hN), coeff_cleared_eq_indexed_sum t n hn]
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  rw [← Finset.prod_subset (Finset.range_mono hN) (f := cubeFactorCoefficient t N r k) (by
    intro i hi hni
    have hiN := Finset.mem_range.mp hi
    have hni' : n ≤ i := by simpa only [Finset.mem_range, not_lt] using hni
    exact cubeFactorCoefficient_unused t N r k i (hn.trans hni') (hk i hni' hiN))]
  apply Finset.prod_congr rfl
  intro i hi
  exact cubeFactorCoefficient_padding t n N hn hN r k i (Finset.mem_range.mp hi)

end LeanCanny.ETR.Term

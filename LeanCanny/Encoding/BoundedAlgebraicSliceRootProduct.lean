/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceRootProductSource
public import LeanCanny.Encoding.BoundedAlgebraicFiberRoot

/-! # A nonzero native root polynomial for an indexed algebraic-slice family

Specialized zero factors are replaced by one before taking the product. At
every valid base root, the result is nonzero and its roots are exactly the
union of the factors' distinct real roots. Every nonzero factor divides it.
The product coefficients, binary controls, and distinct-root count are native.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSliceRootProduct
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical BigOperators

noncomputable def family (P : Readers) (Q : BivariateQueryProductBits.Family) : Family :=
  ofIndexedProduct (BoundedAlgebraicSliceRootProductSource.family P Q)

noncomputable def access {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    (family P Q).Access := ofIndexedProductAccess (BoundedAlgebraicSliceRootProductSource.access h A ha)

def lift (u : List Bool) : List Bool := signQuery (pair u u)
theorem lift_FP : lift ∈ FP := mem_FP_comp (mem_FP_pair id_mem_FP id_mem_FP) signQuery_FP

noncomputable def polynomial (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℝ[X] :=
  specialized (P.comp pairFst) (family P Q) (lift u)

theorem product_valid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) :
    polynomial P Q u = ∏ i : Fin (Q.count (pairFst u)),
      if BoundedAlgebraicSliceIndexed.value P Q u i.val = 0 then 1 else BoundedAlgebraicSliceIndexed.value P Q u i.val := by
  rw [polynomial, lift, specialized_attach_raw, ite_eq_left hu, family]
  have H := ofIndexedProduct_slice (BoundedAlgebraicSliceRootProductSource.family P Q)
    (pair (pairFst u) u) (point P u)
  rw [BoundedAlgebraicSliceRootProductSource.count_eq, pairFst_pair] at H
  rw [H]
  simp only [RootSignQueries.queryPolynomial, BoundedAlgebraicSliceRootProductSource.exponent_eq,
    BoundedAlgebraicSliceRootProductSource.polynomial_eq, show (1 : Fin 3).val = 1 from rfl, pow_one]
  apply Finset.prod_congr rfl
  intro i _
  unfold BoundedAlgebraicSliceRootProductSource.factor
  simp only [pairFst_pair, pairSnd_pair]
  by_cases hi : BoundedAlgebraicSliceIndexed.value P Q u i.val = 0
  · rw [ite_eq_left hi, Polynomial.map_one, ite_eq_left hi]
  · rw [ite_eq_right hi, ite_eq_right hi, BoundedAlgebraicSliceIndexed.value_valid P Q u i.val hu]

theorem polynomial_invalid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∉ valid P) :
    polynomial P Q u = 0 := by
  rw [polynomial, lift, specialized_attach_raw, ite_eq_right hu]

theorem polynomial_ne_zero (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) :
    polynomial P Q u ≠ 0 := by
  rw [product_valid P Q u hu]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs with hi
  · exact one_ne_zero
  · exact hi

theorem factor_zero_or_dvd (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) :
    BoundedAlgebraicSliceIndexed.value P Q u i.val = 0 ∨ BoundedAlgebraicSliceIndexed.value P Q u i.val ∣ polynomial P Q u := by
  by_cases hi : BoundedAlgebraicSliceIndexed.value P Q u i.val = 0
  · exact Or.inl hi
  · right
    rw [product_valid P Q u hu]
    have H := Finset.dvd_prod_of_mem
      (fun j : Fin (Q.count (pairFst u)) => if BoundedAlgebraicSliceIndexed.value P Q u j.val = 0 then 1
        else BoundedAlgebraicSliceIndexed.value P Q u j.val) (Finset.mem_univ i)
    simpa only [ite_eq_right hi] using H

theorem root_iff (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) (y : ℝ) :
    y ∈ (polynomial P Q u).roots.toFinset ↔
      ∃ i : Fin (Q.count (pairFst u)), y ∈ (BoundedAlgebraicSliceIndexed.value P Q u i.val).roots.toFinset := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (polynomial_ne_zero P Q u hu), Polynomial.IsRoot, product_valid P Q u hu,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro i
  by_cases hi : BoundedAlgebraicSliceIndexed.value P Q u i.val = 0
  · simp [hi]
  · rw [ite_eq_right hi, Multiset.mem_toFinset, Polynomial.mem_roots hi, Polynomial.IsRoot]

noncomputable def count (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℕ :=
  RootCount.count (P.comp pairFst) (family P Q) (lift u)

theorem count_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (count P Q u)) :=
  (RootCount.count_evaluator (h.comp pairFst_mem_FP) (access h A ha) (fun c => ha (pairFst c))).precompose lift lift_FP

theorem count_bound (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    count P Q u ≤ 2 * Q.count (pairFst u) * Q.degree (pairFst u) := by
  have H := BoundedAlgebraicFiberRoot.count_le_degree (P.comp pairFst) (family P Q) (lift u)
  simpa only [count, family, ofIndexedProduct, BoundedAlgebraicSliceRootProductSource.family,
    lift, signQuery, pairFst_pair] using H

end LeanCanny.Encoding.BoundedAlgebraicSliceRootProduct

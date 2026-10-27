/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductSource
public import LeanCanny.Encoding.BoundedCriticalSampleFiberRoot

/-! # A nonzero native root polynomial for an indexed algebraic-slice family

Specialized zero factors are replaced by one before taking the product. At
every valid base root, the result is nonzero and its roots are exactly the
union of the factors' distinct real roots. Every nonzero factor divides it.
The product coefficients, binary controls, and distinct-root count are native.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSliceRootProduct
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family ofIndexedProduct ofIndexedProductAccess ofIndexedProduct_slice)
open BoundedCriticalSampleSlice
open scoped Classical BigOperators

noncomputable def family (P : Readers) (Q : BivariateQueryProductBits.Family) : Family :=
  (ofIndexedProduct (BoundedCriticalSampleSliceRootProductSource.family P Q)).comp
    BoundedCriticalSampleSliceIndexed.sourceContext

noncomputable def access {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    (family P Q).Access :=
  (ofIndexedProductAccess (BoundedCriticalSampleSliceRootProductSource.access h A ha)).comp
    BoundedCriticalSampleSliceIndexed.sourceContext BoundedCriticalSampleSliceIndexed.sourceContext_FP

def lift (u : List Bool) : List Bool := attach u u
theorem lift_FP : lift ∈ FP := by polytime [lift, attach]

noncomputable def polynomial (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℝ[X] :=
  specialized P (family P Q) (lift u)

theorem product_valid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) :
    polynomial P Q u = ∏ i : Fin (Q.count (context u)),
      if BoundedCriticalSampleSliceIndexed.value P Q u i.val = 0 then 1 else BoundedCriticalSampleSliceIndexed.value P Q u i.val := by
  have hv : lift u ∈ valid P := (attach_valid P u u).mpr hu
  rw [polynomial, specialized, ite_eq_left hv, family, Family.slice_comp]
  have hc : BoundedCriticalSampleSliceIndexed.sourceContext (context (lift u)) = pair (context u) u := by
    simp only [BoundedCriticalSampleSliceIndexed.sourceContext, context, lift, attach, dropRecord, pairFst_pair, pairSnd_pair]
  rw [hc]
  have H := ofIndexedProduct_slice (BoundedCriticalSampleSliceRootProductSource.family P Q)
    (pair (context u) u) (point P (pairFst u))
  rw [BoundedCriticalSampleSliceRootProductSource.count_eq, pairFst_pair] at H
  simp only [lift, attach, pairFst_pair]
  rw [H]
  simp only [RootSignQueries.queryPolynomial, BoundedCriticalSampleSliceRootProductSource.exponent_eq,
    BoundedCriticalSampleSliceRootProductSource.polynomial_eq, show (1 : Fin 3).val = 1 from rfl, pow_one]
  apply Finset.prod_congr rfl
  intro i _
  unfold BoundedCriticalSampleSliceRootProductSource.factor
  simp only [pairFst_pair, pairSnd_pair]
  by_cases hi : BoundedCriticalSampleSliceIndexed.value P Q u i.val = 0
  · rw [ite_eq_left hi, Polynomial.map_one, ite_eq_left hi]
  · rw [ite_eq_right hi, ite_eq_right hi, BoundedCriticalSampleSliceIndexed.value_valid P Q u i.val hu]

theorem polynomial_invalid (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∉ valid P) :
    polynomial P Q u = 0 := by
  have hv : lift u ∉ valid P := mt (attach_valid P u u).mp hu
  rw [polynomial, specialized, ite_eq_right hv]

theorem polynomial_ne_zero (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) :
    polynomial P Q u ≠ 0 := by
  rw [product_valid P Q u hu]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split_ifs with hi
  · exact one_ne_zero
  · exact hi

theorem factor_zero_or_dvd (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (context u))) :
    BoundedCriticalSampleSliceIndexed.value P Q u i.val = 0 ∨ BoundedCriticalSampleSliceIndexed.value P Q u i.val ∣ polynomial P Q u := by
  by_cases hi : BoundedCriticalSampleSliceIndexed.value P Q u i.val = 0
  · exact Or.inl hi
  · right
    rw [product_valid P Q u hu]
    have H := Finset.dvd_prod_of_mem
      (fun j : Fin (Q.count (context u)) => if BoundedCriticalSampleSliceIndexed.value P Q u j.val = 0 then 1
        else BoundedCriticalSampleSliceIndexed.value P Q u j.val) (Finset.mem_univ i)
    simpa only [ite_eq_right hi] using H

theorem root_iff (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P) (y : ℝ) :
    y ∈ (polynomial P Q u).roots.toFinset ↔
      ∃ i : Fin (Q.count (context u)), y ∈ (BoundedCriticalSampleSliceIndexed.value P Q u i.val).roots.toFinset := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (polynomial_ne_zero P Q u hu), Polynomial.IsRoot, product_valid P Q u hu,
    Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro i
  by_cases hi : BoundedCriticalSampleSliceIndexed.value P Q u i.val = 0
  · simp [hi]
  · rw [ite_eq_right hi, Multiset.mem_toFinset, Polynomial.mem_roots hi, Polynomial.IsRoot]

noncomputable def count (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) : ℕ :=
  RootCount.count P (family P Q) (lift u)

theorem count_evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (count P Q u)) :=
  (RootCount.count_evaluator h (access h A ha) ha).precompose lift lift_FP

theorem count_bound (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) :
    count P Q u ≤ 2 * Q.count (context u) * Q.degree (context u) := by
  have H := BoundedCriticalSampleFiberRoot.count_le_degree P (family P Q) (lift u)
  simpa only [count, family, ofIndexedProduct, BoundedCriticalSampleSliceRootProductSource.family,
    Family.comp, BoundedCriticalSampleSliceIndexed.sourceContext,
    context, lift, attach, dropRecord, pairFst_pair, pairSnd_pair] using H

end LeanCanny.Encoding.BoundedCriticalSampleSliceRootProduct

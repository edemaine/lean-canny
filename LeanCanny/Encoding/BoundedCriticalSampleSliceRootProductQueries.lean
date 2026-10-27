/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceRootProduct
public import LeanCanny.Encoding.BoundedCriticalSampleFiberRootReindex
public import LeanCanny.Encoding.BoundedCriticalSampleFiberCellQueries

/-! # Uniform native factor-sign queries on the constructed root cells

The input contains a base-root query, a factor index, and a root ordinal of
the zero-aware product. All root-product coefficients and factor selection
tests are recomputed by native children. The parameter and ordered root are
unchanged by attaching the requested factor index.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductQueries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Set
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedCriticalSampleSliceRootProduct
open scoped Classical

def testContext (v : List Bool) : List Bool := pair (dropRecord (dropRecord v)) (pairSnd (pairSnd v))
theorem testContext_FP : testContext ∈ FP := by polytime [testContext, dropRecord]

noncomputable def testFamily (Q : BivariateQueryProductBits.Family) : Family :=
  (BoundedAlgebraicSliceIndexed.family Q).comp testContext
noncomputable def testAccess {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) :
    (testFamily Q).Access := (BoundedAlgebraicSliceIndexed.access A).comp testContext testContext_FP

def query (q : List Bool) : List Bool := pair
  (attach (lift (pairFst q)) (pairFst (pairSnd q))) (pairSnd (pairSnd q))
theorem query_FP : query ∈ FP := by
  have hl := mem_FP_comp pairFst_mem_FP lift_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have H := mem_FP_pair (mem_FP_pair (mem_FP_comp hl pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp hl pairSnd_mem_FP) hi)) hr
  exact mem_FP_of_eq H (fun q => by simp only [query, attach, Function.comp_apply])

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (fromLeft : Bool) : List Bool → List Bool :=
  BoundedCriticalSampleFiberLocalSign.value P ((family P Q).comp dropRecord) (testFamily Q) fromLeft ∘ query

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (fromLeft : Bool) :
    SpaceFunction (value P Q fromLeft) :=
  (BoundedCriticalSampleFiberLocalSign.evaluator h ((access h A ha).comp dropRecord dropRecord_FP)
    (testAccess A) ha fromLeft).precompose query query_FP

theorem test_specialized (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) :
    specialized P (testFamily Q) (attach (lift u) (BinaryNatCode.encode i)) =
      BoundedCriticalSampleSliceIndexed.value P Q u i := by
  have hv : attach (lift u) (BinaryNatCode.encode i) ∈ valid P ↔ u ∈ valid P := by
    rw [attach_valid, lift, attach_valid]
  by_cases hu : u ∈ valid P
  · rw [specialized, ite_eq_left (hv.mpr hu), BoundedCriticalSampleSliceIndexed.value_valid P Q u i hu]
    simp only [testFamily, Family.slice, Family.comp, testContext, context, dropRecord, lift, attach,
      BoundedAlgebraicSliceIndexed.family, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · rw [specialized, ite_eq_right (fun h => hu (hv.mp h)), BoundedCriticalSampleSliceIndexed.value_invalid P Q u i hu]

noncomputable def root (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (r : Fin (count P Q u)) : {y // y ∈ (polynomial P Q u).roots.toFinset} :=
  BoundedCriticalSampleFiberRoot.root P (family P Q) (lift u) r

attribute [local irreducible] specialized family testFamily polynomial BoundedCriticalSampleSliceIndexed.value root

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ)
    (r : Fin (count P Q u)) (fromLeft : Bool) :
    value P Q fromLeft (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      InfinitesimalSign.encode (if fromLeft then PolynomialLocalSign.left (BoundedCriticalSampleSliceIndexed.value P Q u i) (root P Q u r).val
        else PolynomialLocalSign.right (BoundedCriticalSampleSliceIndexed.value P Q u i) (root P Q u r).val) := by
  let U := lift u
  let W := attach U (BinaryNatCode.encode i)
  let r' : Fin (RootCount.count P ((family P Q).comp dropRecord) W) :=
    ⟨r.val, by simpa only [W, BoundedCriticalSampleFiberRoot.count_attach, U, count] using r.isLt⟩
  have hq : query (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      pair W (BinaryNatCode.encode r'.val) := by
    simp only [query, pairFst_pair, pairSnd_pair, W, U, r']
  have hr := BoundedCriticalSampleFiberRoot.root_value_attach P (family P Q) U (BinaryNatCode.encode i) r' r rfl
  cases fromLeft with
  | false =>
    simp only [value, Function.comp_apply, hq, Bool.false_eq_true, ite_false]
    rw [BoundedCriticalSampleFiberLocalSign.right_packet, test_specialized, hr]
    simp only [root, U]
  | true =>
    simp only [value, Function.comp_apply, hq, ite_true]
    rw [BoundedCriticalSampleFiberLocalSign.left_packet, test_specialized, hr]
    simp only [root, U]

theorem interval_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (context u))) (r t : Fin (count P Q u)) (hrt : t.val = r.val + 1)
    (y : ℝ) (hy : y ∈ Ioo (root P Q u r).val (root P Q u t).val) :
    value P Q false (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r.val))) =
      InfinitesimalSign.encode (SignType.sign ((BoundedCriticalSampleSliceIndexed.value P Q u i.val).eval y)) := by
  let U := lift u
  let W := attach U (BinaryNatCode.encode i.val)
  let r' : Fin (RootCount.count P ((family P Q).comp dropRecord) W) :=
    ⟨r.val, by simpa only [W, BoundedCriticalSampleFiberRoot.count_attach, U, count] using r.isLt⟩
  let t' : Fin (RootCount.count P ((family P Q).comp dropRecord) W) :=
    ⟨t.val, by simpa only [W, BoundedCriticalSampleFiberRoot.count_attach, U, count] using t.isLt⟩
  have hq : query (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r.val))) =
      pair W (BinaryNatCode.encode r'.val) := by
    simp only [query, pairFst_pair, pairSnd_pair, W, U, r']
  have hr := BoundedCriticalSampleFiberRoot.root_value_attach P (family P Q) U (BinaryNatCode.encode i.val) r' r rfl
  have ht := BoundedCriticalSampleFiberRoot.root_value_attach P (family P Q) U (BinaryNatCode.encode i.val) t' t rfl
  have hg : specialized P (testFamily Q) W = BoundedCriticalSampleSliceIndexed.value P Q u i.val :=
    test_specialized P Q u i.val
  have hf : specialized P ((family P Q).comp dropRecord) W = polynomial P Q u := by
    simpa only [W, U, polynomial] using
      specialized_attach P (family P Q) U (BinaryNatCode.encode i.val)
  have hd : specialized P (testFamily Q) W = 0 ∨
      specialized P (testFamily Q) W ∣
        specialized P ((family P Q).comp dropRecord) W := by
    rw [hg, hf]
    exact factor_zero_or_dvd P Q u hu i
  have hy' : y ∈ Ioo (BoundedCriticalSampleFiberRoot.root P ((family P Q).comp dropRecord) W r').val
      (BoundedCriticalSampleFiberRoot.root P ((family P Q).comp dropRecord) W t').val := by
    rw [hr, ht]
    simpa only [root, U] using hy
  have H := BoundedCriticalSampleFiberRootCells.interval_packet _ _ _ W r' t' hrt hd y hy'
  rw [hg] at H
  simpa only [value, Function.comp_apply, hq] using H

end LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductQueries

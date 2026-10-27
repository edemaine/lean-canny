/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceRootProduct
public import LeanCanny.Encoding.BoundedAlgebraicSlicePointReindex
public import LeanCanny.Encoding.BoundedAlgebraicFiberCellQueries

/-! # Uniform native factor-sign queries on the constructed root cells

The input contains a base-root query, a factor index, and a root ordinal of
the zero-aware product. All root-product coefficients and factor selection
tests are recomputed by native children. The parameter and ordered root are
unchanged by attaching the requested factor index.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSliceRootProductQueries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Set
open BoundedAlgebraicSlice BoundedAlgebraicSliceRootProduct
open scoped Classical

noncomputable def testFamily (Q : BivariateQueryProductBits.Family) : Family :=
  (BoundedAlgebraicSliceIndexed.family Q).comp BoundedAlgebraicSliceRootProductSource.originalSource

noncomputable def testAccess {Q : BivariateQueryProductBits.Family} (A : BivariateQueryProductBits.Access Q) :
    (testFamily Q).Access := (BoundedAlgebraicSliceIndexed.access A).comp
      BoundedAlgebraicSliceRootProductSource.originalSource BoundedAlgebraicSliceRootProductSource.originalSource_FP

def query (q : List Bool) : List Bool := pair
  (signQuery (pair (lift (pairFst q)) (pairFst (pairSnd q)))) (pairSnd (pairSnd q))
theorem query_FP : query ∈ FP := by
  have hl := mem_FP_comp pairFst_mem_FP lift_FP
  have hi := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hs := mem_FP_comp (mem_FP_pair hl hi) signQuery_FP
  exact mem_FP_pair hs (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) (fromLeft : Bool) : List Bool → List Bool :=
  BoundedAlgebraicFiberLocalSign.value ((P.comp pairFst).comp pairFst)
    ((family P Q).comp pairFst) (testFamily Q) fromLeft ∘ query

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (fromLeft : Bool) :
    SpaceFunction (value P Q fromLeft) := by
  have E := BoundedAlgebraicFiberLocalSign.evaluator ((h.comp pairFst_mem_FP).comp pairFst_mem_FP)
    ((access h A ha).comp pairFst pairFst_mem_FP) (testAccess A)
    (fun c => ha (pairFst (pairFst c))) fromLeft
  exact E.precompose query query_FP

theorem test_specialized (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) :
    specialized ((P.comp pairFst).comp pairFst) (testFamily Q)
      (signQuery (pair (lift u) (BinaryNatCode.encode i))) = BoundedAlgebraicSliceIndexed.value P Q u i := by
  rw [specialized_attach_raw]
  have hv : lift u ∈ valid (P.comp pairFst) ↔ u ∈ valid P := valid_attach P u u
  by_cases hu : u ∈ valid P
  · rw [ite_eq_left (hv.mpr hu), BoundedAlgebraicSliceIndexed.value_valid P Q u i hu]
    have hp : point (P.comp pairFst) (lift u) = point P u := point_attach P u u
    rw [hp]
    simp only [testFamily, Family.comp, Family.slice, BoundedAlgebraicSliceIndexed.family,
      BoundedAlgebraicSliceRootProductSource.originalSource, lift, signQuery, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · rw [ite_eq_right (fun h => hu (hv.mp h)), BoundedAlgebraicSliceIndexed.value_invalid P Q u i hu]

noncomputable def root (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool)
    (r : Fin (count P Q u)) : {y // y ∈ (polynomial P Q u).roots.toFinset} :=
  BoundedAlgebraicFiberRoot.root (P.comp pairFst) (family P Q) (lift u) r

attribute [local irreducible] specialized family testFamily polynomial BoundedAlgebraicSliceIndexed.value root

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ)
    (r : Fin (count P Q u)) (fromLeft : Bool) :
    value P Q fromLeft (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      InfinitesimalSign.encode (if fromLeft then PolynomialLocalSign.left (BoundedAlgebraicSliceIndexed.value P Q u i) (root P Q u r).val
        else PolynomialLocalSign.right (BoundedAlgebraicSliceIndexed.value P Q u i) (root P Q u r).val) := by
  let U := lift u
  let W := signQuery (pair U (BinaryNatCode.encode i))
  let r' : Fin (RootCount.count ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W) :=
    ⟨r.val, by simpa only [W, BoundedAlgebraicFiberRoot.count_attach, U, count] using r.isLt⟩
  have hq : query (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      pair W (BinaryNatCode.encode r'.val) := by
    simp only [query, pairFst_pair, pairSnd_pair, W, U, r']
  have hr := BoundedAlgebraicFiberRoot.root_value_attach (P.comp pairFst) (family P Q) U (BinaryNatCode.encode i) r' r rfl
  cases fromLeft with
  | false =>
    simp only [value, Function.comp_apply, hq, Bool.false_eq_true, ite_false]
    rw [BoundedAlgebraicFiberLocalSign.right_packet, test_specialized, hr]
    simp only [root, U]
  | true =>
    simp only [value, Function.comp_apply, hq, ite_true]
    rw [BoundedAlgebraicFiberLocalSign.left_packet, test_specialized, hr]
    simp only [root, U]

theorem interval_packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (hu : u ∈ valid P)
    (i : Fin (Q.count (pairFst u))) (r t : Fin (count P Q u)) (hrt : t.val = r.val + 1)
    (y : ℝ) (hy : y ∈ Ioo (root P Q u r).val (root P Q u t).val) :
    value P Q false (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r.val))) =
      InfinitesimalSign.encode (SignType.sign ((BoundedAlgebraicSliceIndexed.value P Q u i.val).eval y)) := by
  let U := lift u
  let W := signQuery (pair U (BinaryNatCode.encode i.val))
  let r' : Fin (RootCount.count ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W) :=
    ⟨r.val, by simpa only [W, BoundedAlgebraicFiberRoot.count_attach, U, count] using r.isLt⟩
  let t' : Fin (RootCount.count ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W) :=
    ⟨t.val, by simpa only [W, BoundedAlgebraicFiberRoot.count_attach, U, count] using t.isLt⟩
  have hq : query (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode r.val))) =
      pair W (BinaryNatCode.encode r'.val) := by
    simp only [query, pairFst_pair, pairSnd_pair, W, U, r']
  have hr := BoundedAlgebraicFiberRoot.root_value_attach (P.comp pairFst) (family P Q) U (BinaryNatCode.encode i.val) r' r rfl
  have ht := BoundedAlgebraicFiberRoot.root_value_attach (P.comp pairFst) (family P Q) U (BinaryNatCode.encode i.val) t' t rfl
  have hg : specialized ((P.comp pairFst).comp pairFst) (testFamily Q) W = BoundedAlgebraicSliceIndexed.value P Q u i.val :=
    test_specialized P Q u i.val
  have hf : specialized ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W = polynomial P Q u := by
    simpa only [W, U, polynomial] using
      specialized_attach_comp (P.comp pairFst) (family P Q) U (BinaryNatCode.encode i.val)
  have hd : specialized ((P.comp pairFst).comp pairFst) (testFamily Q) W = 0 ∨
      specialized ((P.comp pairFst).comp pairFst) (testFamily Q) W ∣
        specialized ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W := by
    rw [hg, hf]
    exact factor_zero_or_dvd P Q u hu i
  have hy' : y ∈ Ioo (BoundedAlgebraicFiberRoot.root ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W r').val
      (BoundedAlgebraicFiberRoot.root ((P.comp pairFst).comp pairFst) ((family P Q).comp pairFst) W t').val := by
    rw [hr, ht]
    simpa only [root, U] using hy
  have H := BoundedAlgebraicFiberRootCells.interval_packet _ _ _ W r' t' hrt hd y hy'
  rw [hg] at H
  simpa only [value, Function.comp_apply, hq] using H

end LeanCanny.Encoding.BoundedAlgebraicSliceRootProductQueries

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductQueries

/-! # Native indexed factor signs at product roots and at zero

These supply point-cell signs and the sign in the unique cell of a rootless
product. Attaching a factor index preserves the original algebraic base.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductPointSign
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedCriticalSampleSliceRootProduct BoundedCriticalSampleSliceRootProductQueries
open scoped Classical

noncomputable def value (P : Readers) (Q : BivariateQueryProductBits.Family) : List Bool → List Bool :=
  BoundedCriticalSampleFiberTestSign.value P
    ((family P Q).comp dropRecord) (testFamily Q) ∘ query

theorem evaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (value P Q) := by
  have E := BoundedCriticalSampleFiberTestSign.evaluator h
    ((access h A ha).comp dropRecord dropRecord_FP) (testAccess A) ha
  exact E.precompose query query_FP

attribute [local irreducible] specialized family testFamily polynomial BoundedCriticalSampleSliceIndexed.value root

theorem packet (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ)
    (r : Fin (count P Q u)) :
    value P Q (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      InfinitesimalSign.encode (SignType.sign ((BoundedCriticalSampleSliceIndexed.value P Q u i).eval (root P Q u r).val)) := by
  let U := lift u
  let W := attach U (BinaryNatCode.encode i)
  let r' : Fin (RootCount.count P ((family P Q).comp dropRecord) W) :=
    ⟨r.val, by simpa only [W, BoundedCriticalSampleFiberRoot.count_attach, U, count] using r.isLt⟩
  have hq : query (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode r.val))) =
      pair W (BinaryNatCode.encode r'.val) := by
    simp only [query, pairFst_pair, pairSnd_pair, W, U, r']
  have hr := BoundedCriticalSampleFiberRoot.root_value_attach P (family P Q) U (BinaryNatCode.encode i) r' r rfl
  simp only [value, Function.comp_apply, hq]
  rw [BoundedCriticalSampleFiberTestSign.value_original, test_specialized, hr]
  simp only [root, U]

def zeroQuery (q : List Bool) : List Bool :=
  pair (BoundedCriticalSampleSliceIndexed.query q) (BinaryNatCode.encode 0)

theorem zeroQuery_FP : zeroQuery ∈ FP :=
  mem_FP_pair BoundedCriticalSampleSliceIndexed.query_FP (constFn_mem_FP _)

noncomputable def zeroValue (P : Readers) (Q : BivariateQueryProductBits.Family) : List Bool → List Bool :=
  coefficientSign P (BoundedCriticalSampleSliceIndexed.family Q) ∘ zeroQuery

theorem zeroEvaluator {P : Readers} (h : P.PolyTime) {Q : BivariateQueryProductBits.Family}
    (A : BivariateQueryProductBits.Access Q) (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (zeroValue P Q) := by
  have E := coefficientSign_evaluator h (BoundedCriticalSampleSliceIndexed.access A) ha
  exact E.precompose zeroQuery zeroQuery_FP

theorem zeroPacket (P : Readers) (Q : BivariateQueryProductBits.Family) (u : List Bool) (i : ℕ) :
    zeroValue P Q (pair u (BinaryNatCode.encode i)) =
      InfinitesimalSign.encode (SignType.sign ((BoundedCriticalSampleSliceIndexed.value P Q u i).eval 0)) := by
  simp only [zeroValue, Function.comp_apply, zeroQuery]
  rw [coefficientSign_packet]
  simp only [BoundedCriticalSampleSliceIndexed.query, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [BoundedCriticalSampleSliceIndexed.value]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  rfl

end LeanCanny.Encoding.BoundedCriticalSampleSliceRootProductPointSign

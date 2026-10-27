/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRecordSpan
public import LeanCanny.Encoding.BoundedAlgebraicFiberRecordSource

/-! # Native sparse child-root moments at actual sample descriptors

Appending a sparse record preserves the selected actual sample and its
original query record. Native bivariate products give the sum of the record
evaluations over all distinct child roots. All raw records are supported,
including concatenations, and invalid descriptors have moment zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRecordMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family ofIndexedProduct ofIndexedProductAccess)
open BoundedCriticalSampleSlice BoundedAlgebraicFiberRecords
open scoped Classical BigOperators
abbrev Root (P : Readers) (F : Family) (u : List Bool) := BoundedCriticalSampleFiberThom.Root P F u
abbrev Feature (F : Family) (u : List Bool) := BoundedCriticalSampleFiberThom.Feature F u

/-- The source sees `pair (pair source originalRecord) sparseRecord`. -/
def recordContext (v : List Bool) : List Bool := pair (dropRecord v) (pairSnd (pairSnd v))
theorem recordContext_FP : recordContext ∈ FP :=
  mem_FP_pair dropRecord_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def productFamily (F : Family) : Family :=
  (ofIndexedProduct (BoundedAlgebraicFiberRecordSource.family F)).comp recordContext
noncomputable def productAccess {F : Family} (A : F.Access) : (productFamily F).Access :=
  (ofIndexedProductAccess (BoundedAlgebraicFiberRecordSource.access A)).comp recordContext recordContext_FP

noncomputable def moment (P : Readers) (F : Family) (q : List Bool) : ℤ := RootSignQueries.tarskiQuery
  (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q))
  (specialized P (productFamily F) (BoundedCriticalSampleFiberThom.query q))

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F q)) := by
  have E := (Tarski.evaluator h (A.comp dropRecord dropRecord_FP) (productAccess A) ha).precompose
    BoundedCriticalSampleFiberThom.query BoundedCriticalSampleFiberThom.query_FP
  exact E.congr (funext fun q => by simp only [moment, Tarski.value, Function.comp_apply])

theorem moment_valid (P : Readers) (F : Family) (u r : List Bool) (hu : u ∈ valid P) :
    moment P F (pair u r) = RootSignQueries.tarskiQuery (specialized P F u)
      (RootSignQueries.queryPolynomial
        (fun i : Fin (recordSlots F (pair (context u) r)) =>
          (Polynomial.derivative^[order F (pair (context u) r) i.val]) (specialized P F u))
        (fun i => exponent F (pair (context u) r) i.val)) := by
  have hv := (attach_valid P u r).mpr hu
  have hc : recordContext (context (attach u r)) = pair (context u) r := by
    simp only [recordContext, context, attach, dropRecord, pairFst_pair, pairSnd_pair]
  have hp : F.slice (context u) (point P (pairFst (attach u r))) = specialized P F u := by
    simp only [attach, pairFst_pair, specialized, ite_eq_left hu]
  have ht := BoundedAlgebraicFiberRecordSource.product_slice F (pair (context u) r)
    (point P (pairFst (attach u r)))
  rw [pairFst_pair, hp] at ht
  have hs : specialized P (productFamily F) (attach u r) = RootSignQueries.queryPolynomial
      (fun i : Fin (recordSlots F (pair (context u) r)) =>
        (Polynomial.derivative^[order F (pair (context u) r) i.val]) (specialized P F u))
      (fun i => exponent F (pair (context u) r) i.val) := by
    rw [specialized, ite_eq_left hv, productFamily, Family.slice_comp, hc]
    exact ht
  simp only [moment, BoundedCriticalSampleFiberThom.query, pairFst_pair, pairSnd_pair, specialized_attach, hs]

theorem moment_invalid (P : Readers) (F : Family) (u r : List Bool) (hu : u ∉ valid P) : moment P F (pair u r) = 0 := by
  simp only [moment, BoundedCriticalSampleFiberThom.query, pairFst_pair, pairSnd_pair, specialized_attach]
  rw [specialized, ite_eq_right hu]
  simp only [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Polynomial.roots_zero,
    Multiset.toFinset_zero, Finset.sum_empty]

theorem signature_apply (P : Readers) (F : Family) (u : List Bool) (x : Root P F u) (i : Feature F u) :
    BoundedCriticalSampleFiberThom.signature P F u x i =
      SignType.sign (((Polynomial.derivative^[i.val]) (specialized P F u)).eval x.val) := rfl

theorem factor_eq (P : Readers) (F : Family) (u r : List Bool) (i : ℕ)
    (hi : i < recordSlots F (pair (context u) r)) (x : Root P F u) :
    (SignType.sign (((Polynomial.derivative^[order F (pair (context u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (context u) r) i).val =
      SparseFeatureRecords.factor (Nat.succ_pos _) (fun k : Feature F u =>
        (BoundedCriticalSampleFiberThom.signature P F u x k : ℚ)) (SparseFeatureRecords.coordinate (width F (context u)) r i) := by
  have hs := slot_coordinate F (context u) r i hi
  by_cases hz : SparseFeatureRecords.coordinate (width F (context u)) r i = 0
  · simp only [exponent, hs, hz, ite_true, Fin.val_zero, pow_zero, SparseFeatureRecords.factor_zero]
  · rw [exponent, ite_eq_right (by rwa [hs]), show (1 : Fin 3).val = 1 from rfl, pow_one,
      SparseFeatureRecords.factor, ite_eq_right hz, signature_apply]
    simp only [order, hs, pairFst_pair, SparseFeatureRecords.pick, Nat.succ_sub_one]

private theorem tarski_sum (P : Readers) (F : Family) (u : List Bool) (Q : ℝ[X]) :
    (RootSignQueries.tarskiQuery (specialized P F u) Q : ℚ) =
      ∑ x : Root P F u, ((SignType.sign (Q.eval x.val) : ℤ) : ℚ) := by
  rw [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Int.cast_sum]
  change (∑ x ∈ RootCount.roots P F u, ((SignType.sign (Q.eval x) : ℤ) : ℚ)) = _
  rw [← Finset.sum_coe_sort]

theorem moment_eq_sum_values (P : Readers) (F : Family) (u r : List Bool) :
    (moment P F (pair u r) : ℚ) = ∑ x : Root P F u,
      SparseFeatureRecords.value (Nat.succ_pos _) (recordSlots F (pair (context u) r)) (width F (context u))
        (fun i : Feature F u => (BoundedCriticalSampleFiberThom.signature P F u x i : ℚ)) r := by
  by_cases hu : u ∈ valid P
  · rw [moment_valid P F u r hu, tarski_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [RootSignQueries.sign_eval_queryPolynomial, Int.cast_prod, Int.cast_pow,
      SignType.intCast_cast, SparseFeatureRecords.value]
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ =>
      (SignType.sign (((Polynomial.derivative^[order F (pair (context u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (context u) r) i).val) (recordSlots F (pair (context u) r))]
    exact Finset.prod_congr rfl (fun i hi => factor_eq P F u r i (Finset.mem_range.mp hi) x)
  · rw [moment_invalid P F u r hu, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hx := x.property
    simp only [RootCount.roots, specialized, ite_eq_right hu, Polynomial.roots_zero,
      Multiset.toFinset_zero, Finset.notMem_empty] at hx

theorem moment_eq_sum_rows (P : Readers) (F : Family) (u r : List Bool) (hr : r.length = length F (context u)) :
    (moment P F (pair u r) : ℚ) = ∑ x : Root P F u, BoundedCriticalSampleFiberRecordSpan.row P F u r x := by
  rw [moment_eq_sum_values, recordSlots_packet F (context u) r hr]
  exact Finset.sum_congr rfl (fun x _ => (BoundedCriticalSampleFiberRecordSpan.row_apply P F u r x).symm)

theorem moment_bound (P : Readers) (F : Family) (q : List Bool) :
    (moment P F q).natAbs ≤ F.degree (context (pairFst q)) := by
  have H := RootSignQueries.tarskiQuery_bounds
    (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q))
    (specialized P (productFamily F) (BoundedCriticalSampleFiberThom.query q))
  have hd : (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree ≤
      F.degree (context (pairFst q)) := by
    simpa only [BoundedCriticalSampleFiberThom.query, specialized_attach] using specialized_degree P F (pairFst q)
  change -((specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree : ℤ) ≤ moment P F q ∧
    moment P F q ≤ ((specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree : ℤ) at H
  omega

end LeanCanny.Encoding.BoundedCriticalSampleFiberRecordMoments

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRecordSource
public import LeanCanny.Encoding.BoundedAlgebraicFiberRecordSpan
public import LeanCanny.Encoding.BoundedAlgebraicSliceAttach

/-! # Native moments of sparse fiber-sign records

All complete slots are read, permitting concatenated records. Their native
Tarski query equals the sum of the record evaluations over the actual fiber
roots on every raw base query, including invalid ordinals.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRecordMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial BoundedAlgebraicSlice
open BoundedAlgebraicFiberRecords
open scoped Classical BigOperators
abbrev Root (P : Readers) (F : Family) (u : List Bool) := BoundedAlgebraicFiberThom.Root P F u
abbrev Feature (F : Family) (u : List Bool) := BoundedAlgebraicFiberThom.Feature F u

noncomputable def productFamily (F : Family) : Family := ofIndexedProduct (BoundedAlgebraicFiberRecordSource.family F)
noncomputable def moment (P : Readers) (F : Family) (q : List Bool) : ℤ := RootSignQueries.tarskiQuery
  (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
  (specialized (P.comp pairFst) (productFamily F) (signQuery q))

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F q)) := by
  have E := (Tarski.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP)
    (ofIndexedProductAccess (BoundedAlgebraicFiberRecordSource.access A))
    (fun c => ha (pairFst c))).precompose signQuery signQuery_FP
  exact E.congr (funext fun q => by simp only [moment, Tarski.value, productFamily, Function.comp_apply])

theorem moment_valid (P : Readers) (F : Family) (u r : List Bool) (hu : u ∈ valid P) :
    moment P F (pair u r) = RootSignQueries.tarskiQuery (specialized P F u)
      (RootSignQueries.queryPolynomial
        (fun i : Fin (recordSlots F (pair (pairFst u) r)) =>
          (Polynomial.derivative^[order F (pair (pairFst u) r) i.val]) (specialized P F u))
        (fun i => exponent F (pair (pairFst u) r) i.val)) := by
  rw [moment, specialized_attach_comp, specialized_attach_raw, ite_eq_left hu]
  unfold productFamily
  have H := BoundedAlgebraicFiberRecordSource.product_slice F (pair (pairFst u) r) (point P u)
  rw [pairFst_pair] at H
  rw [H]
  have hp : F.slice (pairFst u) (point P u) = specialized P F u := by rw [specialized, ite_eq_left hu]
  rw [hp]

theorem moment_invalid (P : Readers) (F : Family) (u r : List Bool) (hu : u ∉ valid P) : moment P F (pair u r) = 0 := by
  rw [moment, specialized_attach_comp, specialized, ite_eq_right hu]
  simp only [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.sum_empty]

theorem signature_apply (P : Readers) (F : Family) (u : List Bool) (x : Root P F u) (i : Feature F u) :
    BoundedAlgebraicFiberThom.signature P F u x i =
      SignType.sign (((Polynomial.derivative^[i.val]) (specialized P F u)).eval x.val) := rfl

theorem factor_eq (P : Readers) (F : Family) (u r : List Bool) (i : ℕ)
    (hi : i < recordSlots F (pair (pairFst u) r)) (x : Root P F u) :
    (SignType.sign (((Polynomial.derivative^[order F (pair (pairFst u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (pairFst u) r) i).val =
      SparseFeatureRecords.factor (Nat.succ_pos _) (fun k : Feature F u =>
        (BoundedAlgebraicFiberThom.signature P F u x k : ℚ)) (SparseFeatureRecords.coordinate (width F (pairFst u)) r i) := by
  have hs := slot_coordinate F (pairFst u) r i hi
  by_cases hz : SparseFeatureRecords.coordinate (width F (pairFst u)) r i = 0
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
      SparseFeatureRecords.value (Nat.succ_pos _) (recordSlots F (pair (pairFst u) r)) (width F (pairFst u))
        (fun i : Feature F u => (BoundedAlgebraicFiberThom.signature P F u x i : ℚ)) r := by
  by_cases hu : u ∈ valid P
  · rw [moment_valid P F u r hu, tarski_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [RootSignQueries.sign_eval_queryPolynomial, Int.cast_prod, Int.cast_pow, SignType.intCast_cast, SparseFeatureRecords.value]
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ =>
      (SignType.sign (((Polynomial.derivative^[order F (pair (pairFst u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (pairFst u) r) i).val) (recordSlots F (pair (pairFst u) r))]
    exact Finset.prod_congr rfl (fun i hi => factor_eq P F u r i (Finset.mem_range.mp hi) x)
  · rw [moment_invalid P F u r hu, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hx := x.property
    simp only [RootCount.roots, specialized, ite_eq_right hu, Polynomial.roots_zero, Multiset.toFinset_zero,
      Finset.notMem_empty] at hx

theorem moment_eq_sum_rows (P : Readers) (F : Family) (u r : List Bool) (hr : r.length = length F (pairFst u)) :
    (moment P F (pair u r) : ℚ) = ∑ x : Root P F u, BoundedAlgebraicFiberRecordSpan.row P F u r x := by
  rw [moment_eq_sum_values, recordSlots_packet F (pairFst u) r hr]
  exact Finset.sum_congr rfl (fun x _ => (BoundedAlgebraicFiberRecordSpan.row_apply P F u r x).symm)

theorem moment_bound (P : Readers) (F : Family) (q : List Bool) :
    (moment P F q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  have hd : (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree ≤ F.degree (pairFst (pairFst q)) := by
    simpa only [Family.comp, signQuery, pairFst_pair] using specialized_degree (P.comp pairFst) (F.comp pairFst) (signQuery q)
  have H := RootSignQueries.tarskiQuery_bounds (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
    (specialized (P.comp pairFst) (productFamily F) (signQuery q))
  change -((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) ≤ moment P F q ∧
    moment P F q ≤ ((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) at H
  omega

end LeanCanny.Encoding.BoundedAlgebraicFiberRecordMoments

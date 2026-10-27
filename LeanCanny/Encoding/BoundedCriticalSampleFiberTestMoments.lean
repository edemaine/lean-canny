/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberBasisMoments
public import LeanCanny.Encoding.BoundedCriticalSampleFiberBasisGram
public import LeanCanny.Encoding.BoundedAlgebraicSliceProducts

/-! # Native general-test moments on actual-sample child roots

The sparse records and test polynomial specialize at the same actual sample.
Attaching a moment record preserves the parent descriptor and original record.
No test sign or weighted-moment oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family product productAccess product_slice)
open BoundedCriticalSampleSlice BoundedAlgebraicFiberRecords
open scoped Classical BigOperators

noncomputable def sign (P : Readers) (G : Family) (u : List Bool) (x : ℝ) : SignType :=
  SignType.sign ((specialized P G u).eval x)

noncomputable def productFamily (F G : Family) : Family :=
  product (BoundedCriticalSampleFiberRecordMoments.productFamily F) (G.comp dropRecord)

noncomputable def rawMoment (P : Readers) (F G : Family) (q : List Bool) : ℤ := RootSignQueries.tarskiQuery
  (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q))
  (specialized P (productFamily F G) (BoundedCriticalSampleFiberThom.query q))

theorem raw_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (rawMoment P F G q)) := by
  have E := (Tarski.evaluator h (A.comp dropRecord dropRecord_FP)
    (productAccess (BoundedCriticalSampleFiberRecordMoments.productAccess A)
      (B.comp dropRecord dropRecord_FP)) ha).precompose
        BoundedCriticalSampleFiberThom.query BoundedCriticalSampleFiberThom.query_FP
  exact E.congr (funext fun q => by simp only [rawMoment, Tarski.value, productFamily, Function.comp_apply])

theorem raw_invalid (P : Readers) (F G : Family) (u r : List Bool) (hu : u ∉ valid P) :
    rawMoment P F G (pair u r) = 0 := by
  simp only [rawMoment, BoundedCriticalSampleFiberThom.query, pairFst_pair, pairSnd_pair, specialized_attach]
  rw [specialized, ite_eq_right hu]
  simp only [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Polynomial.roots_zero,
    Multiset.toFinset_zero, Finset.sum_empty]

theorem raw_bound (P : Readers) (F G : Family) (q : List Bool) :
    (rawMoment P F G q).natAbs ≤ F.degree (context (pairFst q)) := by
  have hd : (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree ≤
      F.degree (context (pairFst q)) := by
    simpa only [BoundedCriticalSampleFiberThom.query, specialized_attach] using specialized_degree P F (pairFst q)
  have H := RootSignQueries.tarskiQuery_bounds
    (specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q))
    (specialized P (productFamily F G) (BoundedCriticalSampleFiberThom.query q))
  change -((specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree : ℤ) ≤ rawMoment P F G q ∧
    rawMoment P F G q ≤ ((specialized P (F.comp dropRecord) (BoundedCriticalSampleFiberThom.query q)).natDegree : ℤ) at H
  omega

private theorem product_specialized (P : Readers) (F G : Family) (u : List Bool) :
    specialized P (product F G) u = specialized P F u * specialized P G u := by
  by_cases hu : u ∈ valid P
  · simp only [specialized, ite_eq_left hu, product_slice]
  · simp only [specialized, ite_eq_right hu, zero_mul]

theorem raw_valid (P : Readers) (F G : Family) (u r : List Bool) (hu : u ∈ valid P) :
    rawMoment P F G (pair u r) = RootSignQueries.tarskiQuery (specialized P F u)
      (RootSignQueries.queryPolynomial
        (fun i : Fin (recordSlots F (pair (context u) r)) =>
          (Polynomial.derivative^[order F (pair (context u) r) i.val]) (specialized P F u))
        (fun i => exponent F (pair (context u) r) i.val) * specialized P G u) := by
  have hv := (attach_valid P u r).mpr hu
  have hc : BoundedCriticalSampleFiberRecordMoments.recordContext (context (attach u r)) = pair (context u) r := by
    simp only [BoundedCriticalSampleFiberRecordMoments.recordContext, context, attach, dropRecord, pairFst_pair, pairSnd_pair]
  have hp : F.slice (context u) (point P (pairFst (attach u r))) = specialized P F u := by
    simp only [attach, pairFst_pair, specialized, ite_eq_left hu]
  have ht := BoundedAlgebraicFiberRecordSource.product_slice F (pair (context u) r) (point P (pairFst (attach u r)))
  rw [pairFst_pair, hp] at ht
  have hs : specialized P (BoundedCriticalSampleFiberRecordMoments.productFamily F) (attach u r) =
      RootSignQueries.queryPolynomial
        (fun i : Fin (recordSlots F (pair (context u) r)) =>
          (Polynomial.derivative^[order F (pair (context u) r) i.val]) (specialized P F u))
        (fun i => exponent F (pair (context u) r) i.val) := by
    rw [specialized, ite_eq_left hv, BoundedCriticalSampleFiberRecordMoments.productFamily, Family.slice_comp, hc]
    exact ht
  simp only [rawMoment, BoundedCriticalSampleFiberThom.query, pairFst_pair, pairSnd_pair, specialized_attach,
    productFamily, product_specialized, hs]

private theorem tarski_sum (P : Readers) (F : Family) (u : List Bool) (Q : ℝ[X]) :
    (RootSignQueries.tarskiQuery (specialized P F u) Q : ℚ) =
      ∑ x : BoundedCriticalSampleFiberRecordSpan.Root P F u, ((SignType.sign (Q.eval x.val) : ℤ) : ℚ) := by
  rw [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Int.cast_sum]
  change (∑ x ∈ RootCount.roots P F u, ((SignType.sign (Q.eval x) : ℤ) : ℚ)) = _
  rw [← Finset.sum_coe_sort]

theorem raw_packet (P : Readers) (F G : Family) (u r : List Bool) :
    (rawMoment P F G (pair u r) : ℚ) = ∑ x : BoundedCriticalSampleFiberRecordSpan.Root P F u,
      SparseFeatureRecords.value (Nat.succ_pos _) (recordSlots F (pair (BoundedCriticalSampleSlice.context u) r)) (width F (context u))
        (fun i => (BoundedCriticalSampleFiberThom.signature P F u x i : ℚ)) r * (sign P G u x.val : ℚ) := by
  by_cases hu : u ∈ valid P
  · rw [raw_valid P F G u r hu, tarski_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Polynomial.eval_mul, sign_mul, SignType.coe_mul, Int.cast_mul,
      RootSignQueries.sign_eval_queryPolynomial]
    simp only [Int.cast_prod, Int.cast_pow, SignType.intCast_cast, SparseFeatureRecords.value, sign]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ =>
      (SignType.sign (((Polynomial.derivative^[order F (pair (BoundedCriticalSampleSlice.context u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (BoundedCriticalSampleSlice.context u) r) i).val) (recordSlots F (pair (BoundedCriticalSampleSlice.context u) r))]
    exact Finset.prod_congr rfl (fun i hi => BoundedCriticalSampleFiberRecordMoments.factor_eq P F u r i
      (Finset.mem_range.mp hi) x)
  · rw [raw_invalid P F G u r hu, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hx := x.property
    simp only [RootCount.roots, specialized, ite_eq_right hu, Polynomial.roots_zero,
      Multiset.toFinset_zero, Finset.notMem_empty] at hx

noncomputable def source (P : Readers) (F : Family) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedCriticalSampleFiberBasisMoments.record P F (BoundedCriticalSampleFiberBasisGram.leftQuery q) ++
    BoundedCriticalSampleFiberBasisMoments.record P F (BoundedCriticalSampleFiberBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P F) := by
  have E := BoundedCriticalSampleFiberBasisMoments.record_evaluator h A ha
  have L := E.precompose BoundedCriticalSampleFiberBasisGram.leftQuery BoundedCriticalSampleFiberBasisGram.leftQuery_FP
  have R := E.precompose BoundedCriticalSampleFiberBasisGram.rightQuery BoundedCriticalSampleFiberBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (F : Family) (G : Family) (q : List Bool) : ℤ := rawMoment P F G (source P F q)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access) {G : Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F G q)) :=
  (source_evaluator h A ha).chain (raw_evaluator h A B ha)

theorem moment_bound (P : Readers) (F : Family) (G : Family) (q : List Bool) :
    (moment P F G q).natAbs ≤ F.degree (BoundedCriticalSampleSlice.context (pairFst q)) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P F G (source P F q)

theorem moment_packet (P : Readers) (F : Family) (G : Family) (c : List Bool) (i j : Fin (RootCount.count P F c)) :
    (moment P F G (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedCriticalSampleFiberRecordSpan.Root P F c, BoundedCriticalSampleFiberRankBasis.selected P F c i x *
        BoundedCriticalSampleFiberRankBasis.selected P F c j x * (sign P G c x.val : ℚ) := by
  let a := BoundedCriticalSampleFiberBasisMoments.selectedRecord P F c i
  let b := BoundedCriticalSampleFiberBasisMoments.selectedRecord P F c j
  have ha : a.length = BoundedAlgebraicFiberRecords.length F (BoundedCriticalSampleSlice.context c) := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedAlgebraicFiberRecords.length F (BoundedCriticalSampleSlice.context c) := ImplicitGraph.length_word _ _
  have hs : source P F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, BoundedCriticalSampleFiberBasisGram.leftQuery, BoundedCriticalSampleFiberBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, BoundedCriticalSampleFiberBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedAlgebraicFiberRecords.recordSlots F (pair (BoundedCriticalSampleSlice.context c) (a ++ b)) =
      BoundedAlgebraicFiberRecords.slots F (BoundedCriticalSampleSlice.context c) + BoundedAlgebraicFiberRecords.slots F (BoundedCriticalSampleSlice.context c) := by
    simp only [BoundedAlgebraicFiberRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedAlgebraicFiberRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedAlgebraicFiberRecords.width_pos F (BoundedCriticalSampleSlice.context c))
  rw [hc]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedCriticalSampleFiberBasisMoments.selected_value, BoundedCriticalSampleFiberBasisMoments.selected_value]

end LeanCanny.Encoding.BoundedCriticalSampleFiberTestMoments

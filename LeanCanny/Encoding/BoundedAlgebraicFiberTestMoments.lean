/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberBasisMoments
public import LeanCanny.Encoding.BoundedAlgebraicFiberBasisGram
public import LeanCanny.Encoding.BoundedAlgebraicSliceProducts

/-! # Native selected-basis moments weighted by an arbitrary bivariate test

The original test reader is multiplied with the sparse derivative product
before algebraic specialization. Neither pointwise test signs nor weighted
moments are supplied as inputs. Invalid base ordinals have no roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice BoundedAlgebraicFiberRecords
open scoped Classical BigOperators

noncomputable def sign (P : Readers) (G : Family) (u : List Bool) (x : ℝ) : SignType :=
  SignType.sign ((specialized P G u).eval x)

noncomputable def productFamily (F G : Family) : Family :=
  product (BoundedAlgebraicFiberRecordMoments.productFamily F) (G.comp pairFst)

noncomputable def rawMoment (P : Readers) (F G : Family) (q : List Bool) : ℤ := RootSignQueries.tarskiQuery
  (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
  (specialized (P.comp pairFst) (productFamily F G) (signQuery q))

theorem raw_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (rawMoment P F G q)) := by
  have E := (Tarski.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP)
    (productAccess (ofIndexedProductAccess (BoundedAlgebraicFiberRecordSource.access A))
      (B.comp pairFst pairFst_mem_FP)) (fun c => ha (pairFst c))).precompose signQuery signQuery_FP
  exact E.congr (funext fun q => by
    simp only [rawMoment, Tarski.value, productFamily, BoundedAlgebraicFiberRecordMoments.productFamily,
      Function.comp_apply])

theorem raw_invalid (P : Readers) (F G : Family) (u r : List Bool) (hu : u ∉ valid P) :
    rawMoment P F G (pair u r) = 0 := by
  rw [rawMoment, specialized_attach_comp, specialized, ite_eq_right hu]
  simp only [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Polynomial.roots_zero,
    Multiset.toFinset_zero, Finset.sum_empty]

theorem raw_bound (P : Readers) (F G : Family) (q : List Bool) :
    (rawMoment P F G q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  have hd : (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree ≤
      F.degree (pairFst (pairFst q)) := by
    simpa only [Family.comp, signQuery, pairFst_pair] using
      specialized_degree (P.comp pairFst) (F.comp pairFst) (signQuery q)
  have H := RootSignQueries.tarskiQuery_bounds (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
    (specialized (P.comp pairFst) (productFamily F G) (signQuery q))
  change -((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) ≤ rawMoment P F G q ∧
    rawMoment P F G q ≤ ((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) at H
  omega

theorem raw_valid (P : Readers) (F G : Family) (u r : List Bool) (hu : u ∈ valid P) :
    rawMoment P F G (pair u r) = RootSignQueries.tarskiQuery (specialized P F u)
      (RootSignQueries.queryPolynomial
        (fun i : Fin (recordSlots F (pair (pairFst u) r)) =>
          (Polynomial.derivative^[order F (pair (pairFst u) r) i.val]) (specialized P F u))
        (fun i => exponent F (pair (pairFst u) r) i.val) * specialized P G u) := by
  rw [rawMoment, specialized_attach_comp, specialized_attach_raw, ite_eq_left hu,
    productFamily, product_slice, Family.slice_comp, pairFst_pair]
  have H := BoundedAlgebraicFiberRecordSource.product_slice F (pair (pairFst u) r) (point P u)
  rw [pairFst_pair] at H
  rw [BoundedAlgebraicFiberRecordMoments.productFamily, H]
  have hf : F.slice (pairFst u) (point P u) = specialized P F u := by rw [specialized, ite_eq_left hu]
  have hg : G.slice (pairFst u) (point P u) = specialized P G u := by rw [specialized, ite_eq_left hu]
  rw [hf, hg]

private theorem tarski_sum (P : Readers) (F : Family) (u : List Bool) (Q : ℝ[X]) :
    (RootSignQueries.tarskiQuery (specialized P F u) Q : ℚ) =
      ∑ x : BoundedAlgebraicFiberRecordSpan.Root P F u, ((SignType.sign (Q.eval x.val) : ℤ) : ℚ) := by
  rw [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Int.cast_sum]
  change (∑ x ∈ RootCount.roots P F u, ((SignType.sign (Q.eval x) : ℤ) : ℚ)) = _
  rw [← Finset.sum_coe_sort]

theorem raw_packet (P : Readers) (F G : Family) (u r : List Bool) :
    (rawMoment P F G (pair u r) : ℚ) = ∑ x : BoundedAlgebraicFiberRecordSpan.Root P F u,
      SparseFeatureRecords.value (Nat.succ_pos _) (recordSlots F (pair (pairFst u) r)) (width F (pairFst u))
        (fun i => (BoundedAlgebraicFiberThom.signature P F u x i : ℚ)) r * (sign P G u x.val : ℚ) := by
  by_cases hu : u ∈ valid P
  · rw [raw_valid P F G u r hu, tarski_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Polynomial.eval_mul, sign_mul, SignType.coe_mul, Int.cast_mul,
      RootSignQueries.sign_eval_queryPolynomial]
    simp only [Int.cast_prod, Int.cast_pow, SignType.intCast_cast, SparseFeatureRecords.value, sign]
    congr 1
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ =>
      (SignType.sign (((Polynomial.derivative^[order F (pair (pairFst u) r) i]) (specialized P F u)).eval x.val) : ℚ) ^
        (exponent F (pair (pairFst u) r) i).val) (recordSlots F (pair (pairFst u) r))]
    exact Finset.prod_congr rfl (fun i hi => BoundedAlgebraicFiberRecordMoments.factor_eq P F u r i
      (Finset.mem_range.mp hi) x)
  · rw [raw_invalid P F G u r hu, Int.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro x _
    have hx := x.property
    simp only [RootCount.roots, specialized, ite_eq_right hu, Polynomial.roots_zero,
      Multiset.toFinset_zero, Finset.notMem_empty] at hx

noncomputable def source (P : Readers) (F : Family) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedAlgebraicFiberBasisMoments.record P F (BoundedAlgebraicFiberBasisGram.leftQuery q) ++
    BoundedAlgebraicFiberBasisMoments.record P F (BoundedAlgebraicFiberBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P F) := by
  have E := BoundedAlgebraicFiberBasisMoments.record_evaluator h A ha
  have L := E.precompose BoundedAlgebraicFiberBasisGram.leftQuery BoundedAlgebraicFiberBasisGram.leftQuery_FP
  have R := E.precompose BoundedAlgebraicFiberBasisGram.rightQuery BoundedAlgebraicFiberBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (F : Family) (G : Family) (q : List Bool) : ℤ := rawMoment P F G (source P F q)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access) {G : Family} (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F G q)) :=
  (source_evaluator h A ha).chain (raw_evaluator h A B ha)

theorem moment_bound (P : Readers) (F : Family) (G : Family) (q : List Bool) :
    (moment P F G q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P F G (source P F q)

theorem moment_packet (P : Readers) (F : Family) (G : Family) (c : List Bool) (i j : Fin (RootCount.count P F c)) :
    (moment P F G (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedAlgebraicFiberRecordSpan.Root P F c, BoundedAlgebraicFiberRankBasis.selected P F c i x *
        BoundedAlgebraicFiberRankBasis.selected P F c j x * (sign P G c x.val : ℚ) := by
  let a := BoundedAlgebraicFiberRootHash.record P F c i
  let b := BoundedAlgebraicFiberRootHash.record P F c j
  have ha : a.length = BoundedAlgebraicFiberRecords.length F (pairFst c) := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedAlgebraicFiberRecords.length F (pairFst c) := ImplicitGraph.length_word _ _
  have hs : source P F (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, BoundedAlgebraicFiberBasisGram.leftQuery, BoundedAlgebraicFiberBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, BoundedAlgebraicFiberBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedAlgebraicFiberRecords.recordSlots F (pair (pairFst c) (a ++ b)) =
      BoundedAlgebraicFiberRecords.slots F (pairFst c) + BoundedAlgebraicFiberRecords.slots F (pairFst c) := by
    simp only [BoundedAlgebraicFiberRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedAlgebraicFiberRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedAlgebraicFiberRecords.width_pos F (pairFst c))
  rw [hc]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedAlgebraicFiberBasisMoments.selected_value, BoundedAlgebraicFiberBasisMoments.selected_value]

end LeanCanny.Encoding.BoundedAlgebraicFiberTestMoments

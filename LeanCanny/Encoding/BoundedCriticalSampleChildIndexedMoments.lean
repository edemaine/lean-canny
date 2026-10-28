/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildTestMoments

/-! # Polynomial-indexed moments in a fixed regular-child basis

The test context is `pair source queryIndex`. Reindexing drops the query
index only for the original sample filter and selected basis records. The
test polynomial retains that index, so changing it does not change the
parameter polynomial, selected hash, or sample enumeration.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildIndexedMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleChildTestMoments
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count
attribute [local irreducible] BoundedCriticalSampleChildCoordinates.parameter
  PrimitivePairBits.coefficient BoundedCriticalSampleChildRecords.coefficient

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def recordContext (z : List Bool) : List Bool := pair (origin z) (pairSnd z)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem recordContext_FP : recordContext ∈ FP := mem_FP_pair origin_FP pairSnd_mem_FP

noncomputable def records (P : Inputs) : SignPatternBits.Family :=
  (BoundedCriticalSampleChildRecords.family P).comp recordContext

noncomputable def single (P : Inputs) (T : Test) : SignPatternBits.Family :=
  { records P with
    polynomial := fun z _ => T.polynomial (pairFst z)
    pattern := fun _ _ => 0
    count := fun _ => BinaryNatCode.encode 1
    degree := fun z => BinaryNatCode.encode (T.degree (pairFst z))
    mass := fun z => BinaryNatCode.encode (T.mass (pairFst z))
    polynomial_degree := fun z _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact T.polynomial_degree (pairFst z)
    polynomial_mass := fun z _ _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      exact T.polynomial_mass (pairFst z) }

noncomputable def family (P : Inputs) (T : Test) : SignPatternBits.Family := (records P).append (single P T)

theorem records_controls {P : Inputs} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (records P) :=
  SignPatternBits.comp_controls (BoundedCriticalSampleChildRecords.controls h) recordContext_FP
attribute [local irreducible] BoundedCriticalSampleChildThom.massExponent
theorem single_controls {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SignPatternBits.ControlsPolyTime (single P T) := by
  have hd : BinaryFn (fun z => T.degree (pairFst z)) := A.degree_binary.comp pairFst_mem_FP
  have hm : BinaryFn (fun z => T.mass (pairFst z)) := A.mass_binary.comp pairFst_mem_FP
  constructor
  · exact constFn_mem_FP _
  · exact UnaryFn.const 1
  · change (records P).rootDegree ∈ FP
    exact (records_controls h).rootDegree
  · change (fun z => BinaryNatCode.encode (T.degree (pairFst z))) ∈ FP
    exact hd.bits_mem_FP
  · change (records P).rootMass ∈ FP
    exact (records_controls h).rootMass
  · change (fun z => BinaryNatCode.encode (T.mass (pairFst z))) ∈ FP
    exact hm.bits_mem_FP

noncomputable def recordAccess (P : Inputs) : SignPatternBits.Access (records P) :=
  (BoundedCriticalSampleChildRecords.access P).comp recordContext
noncomputable def singleAccess (P : Inputs) {T : Test} (A : T.Access) : SignPatternBits.Access (single P T) where
  rootCoefficient := (recordAccess P).rootCoefficient
  root_eq := (recordAccess P).root_eq
  polynomialCoefficient := A.coefficient ∘ testQuery
  polynomial_eq z _ _ k m hm := by
    simpa only [Function.comp_apply, testQuery, BoundedCriticalSampleChildThom.original,
      BoundedCriticalSampleChildThom.index, pairFst_pair, pairSnd_pair, single] using A.coefficient_eq (pairFst z) k m hm
  pattern _ := []
  pattern_eq _ _ := rfl

noncomputable def rawMoment (P : Inputs) (T : Test) (z : List Bool) : ℤ :=
  BoundedCriticalSampleChildReindexedQueries.moment P origin (family P T) z

theorem raw_evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) := by
  have R : SpaceFunction (recordAccess P).polynomialCoefficient :=
    (BoundedCriticalSampleChildRecords.coefficient_evaluator h).precompose
      (SignPatternBits.compQuery recordContext) (SignPatternBits.compQuery_FP recordContext_FP)
  have S : SpaceFunction (singleAccess P A).polynomialCoefficient := A.evaluator.precompose testQuery testQuery_FP
  exact BoundedCriticalSampleChildReindexedQueries.evaluator h origin_FP ((recordAccess P).append (singleAccess P A))
    (SignPatternBits.append_controls (records_controls h) (single_controls h A))
    (SignPatternBits.appendCoefficient_evaluator (records_controls h) R S)

theorem raw_bound (P : Inputs) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P (origin z) :=
  (BoundedCriticalSampleChildReindexedQueries.moment_bound P origin (family P T) z).trans
    (by simpa only [BoundedCriticalSampleChildThom.labelWidth] using BoundedCriticalSampleChildRegularCount.count_le P (origin z))

theorem raw_packet (P : Inputs) (T : Test) (c d r : List Bool) :
    (rawMoment P T (pair (pair c d) r) : ℚ) = ∑ x : BoundedCriticalSampleChildRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (BoundedCriticalSampleChildRecords.recordSlots P (pair c r))
        (BoundedCriticalSampleChildRecords.width P c)
        (fun i => (BoundedCriticalSampleChildThom.signature P c x i : ℚ)) r * (sign T (pair c d) x.val : ℚ) := by
  rw [rawMoment, BoundedCriticalSampleChildReindexedQueries.moment]
  simp only [BoundedCriticalSampleChildQueries.product]
  simp only [family, SignPatternBits.Family.append, records, single, SignPatternBits.Family.comp,
    recordContext, origin, pairFst_pair, pairSnd_pair, BoundedCriticalSampleChildRecords.family,
    Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, algebraMap_int_eq]
  rw [Int.cast_sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_range_succ]
  simp only [lt_self_iff_false, ite_false, Int.cast_mul, Int.cast_prod, SignType.intCast_cast]
  change (∏ i ∈ Finset.range _, _) * (sign T (pair c d) x.val : ℚ) = _
  congr 1
  unfold SparseFeatureRecords.value
  apply Finset.prod_congr rfl
  intro i hi
  rw [ite_eq_left (Finset.mem_range.mp hi)]
  exact BoundedCriticalSampleChildRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

def leftQuery (q : List Bool) : List Bool := pair (origin q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (origin q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP := mem_FP_pair origin_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP := mem_FP_pair origin_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Inputs) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedCriticalSampleChildBasisMoments.record P (leftQuery q) ++ BoundedCriticalSampleChildBasisMoments.record P (rightQuery q))

theorem source_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (source P) := by
  have E := BoundedCriticalSampleChildBasisMoments.record_evaluator h
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose BoundedCriticalSampleChildTestMoments.finish BoundedCriticalSampleChildTestMoments.finish_FP).congr
    (funext fun q => by simp only [source, BoundedCriticalSampleChildTestMoments.finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Inputs) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h).chain (raw_evaluator h A)

theorem moment_bound (P : Inputs) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P (origin q) := by
  simpa only [moment, source, origin, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Inputs) (T : Test) (c d : List Bool) (i j : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (moment P T (pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedCriticalSampleChildRecordSpan.Root P c, BoundedCriticalSampleChildRankBasis.selected P c i x *
        BoundedCriticalSampleChildRankBasis.selected P c j x * (sign T (pair c d) x.val : ℚ) := by
  let a := BoundedCriticalSampleChildRootHash.record P c i
  let b := BoundedCriticalSampleChildRootHash.record P c j
  have ha : a.length = BoundedCriticalSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedCriticalSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (pair c d) (a ++ b) := by
    simp only [source, leftQuery, rightQuery, origin, pairFst_pair, pairSnd_pair, BoundedCriticalSampleChildBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedCriticalSampleChildRecords.recordSlots P (pair c (a ++ b)) =
      BoundedCriticalSampleChildRecords.slots P c + BoundedCriticalSampleChildRecords.slots P c := by
    simp only [BoundedCriticalSampleChildRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedCriticalSampleChildRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedCriticalSampleChildRecords.width_pos P c)
  rw [hc]
  have ha' : a.length = BoundedCriticalSampleChildRecords.slots P c * BoundedCriticalSampleChildRecords.width P c := by
    simpa only [BoundedCriticalSampleChildRecords.length] using ha
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha',
    BoundedCriticalSampleChildBasisMoments.selected_value, BoundedCriticalSampleChildBasisMoments.selected_value]

end LeanCanny.Encoding.BoundedCriticalSampleChildIndexedMoments

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTestMoments

/-! # Polynomial-indexed moments in a fixed actual-sample basis

The test context is `pair source queryIndex`. Reindexing drops the query
index only for the original sample filter and selected basis records. The
test polynomial retains that index, so changing it does not change the
parameter polynomial, selected hash, or sample enumeration.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleIndexedMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleTestMoments
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter
  PrimitivePairBits.coefficient BoundedCriticalSampleRecords.coefficient

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def recordContext (z : List Bool) : List Bool := pair (origin z) (pairSnd z)
theorem origin_FP : origin ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem recordContext_FP : recordContext ∈ FP := mem_FP_pair origin_FP pairSnd_mem_FP

noncomputable def records (P : Readers) : SignPatternBits.Family :=
  (BoundedCriticalSampleRecords.family P).comp recordContext
noncomputable def filter (P : Readers) : SignPatternBits.Family :=
  (BoundedCriticalSampleCount.family P).comp origin

noncomputable def single (P : Readers) (T : Test) : SignPatternBits.Family :=
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

noncomputable def family (P : Readers) (T : Test) : SignPatternBits.Family := (records P).append (single P T)

theorem records_controls {P : Readers} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (records P) :=
  SignPatternBits.comp_controls (BoundedCriticalSampleRecords.controls h) recordContext_FP
theorem filter_controls {P : Readers} (h : P.PolyTime) : SignPatternBits.ControlsPolyTime (filter P) :=
  SignPatternBits.comp_controls (BoundedCriticalSampleCount.controls h) origin_FP
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalRationalCoordinates.baseHeight BoundedCriticalSampleThom.massExponent
theorem single_controls {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access) :
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

noncomputable def recordAccess (P : Readers) : SignPatternBits.Access (records P) :=
  (BoundedCriticalSampleRecords.access P).comp recordContext
noncomputable def filterAccess (P : Readers) : SignPatternBits.Access (filter P) :=
  (BoundedCriticalSampleCount.access P).comp origin
noncomputable def singleAccess (P : Readers) {T : Test} (A : T.Access) : SignPatternBits.Access (single P T) where
  rootCoefficient := (recordAccess P).rootCoefficient
  root_eq := (recordAccess P).root_eq
  polynomialCoefficient := A.coefficient ∘ testQuery
  polynomial_eq z _ _ k m hm := by
    simpa only [Function.comp_apply, testQuery, BoundedCriticalSampleThom.original,
      BoundedCriticalSampleThom.index, pairFst_pair, pairSnd_pair, single] using A.coefficient_eq (pairFst z) k m hm
  pattern _ := []
  pattern_eq _ _ := rfl

noncomputable def rawMoment (P : Readers) (T : Test) (z : List Bool) : ℤ :=
  FilteredSignProductBits.value (filter P) (family P T) z

theorem filter_roots (P : Readers) (z : List Bool) :
    SignPatternBits.acceptedRoots (filter P) z = BoundedCriticalSampleLabels.rootSet P (origin z) := by
  change SignPatternBits.acceptedRoots (BoundedCriticalSampleCount.family P) (origin z) = _
  exact BoundedCriticalSampleMoments.acceptedRoots_eq P (origin z)

theorem raw_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) := by
  have hq := SignPatternBits.compQuery_FP origin_FP
  have H : SpaceFunction (filterAccess P).rootCoefficient :=
    (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha).precompose
      (SignPatternBits.compQuery origin) hq
  have Q : SpaceFunction (filterAccess P).polynomialCoefficient :=
    ((BoundedCriticalFilterCoefficients.evaluator h ha).precompose
      BoundedCriticalSampleCount.filterQuery BoundedCriticalSampleCount.filterQuery_FP).precompose
        (SignPatternBits.compQuery origin) hq
  have hs : (filterAccess P).pattern ∈ FP := by
    change ((BoundedCriticalSampleCount.access P).pattern ∘ SignPatternBits.compPattern origin) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP origin_FP) (constFn_mem_FP [])
  have R : SpaceFunction (recordAccess P).polynomialCoefficient :=
    (BoundedCriticalSampleRecords.coefficient_evaluator h ha).precompose
      (SignPatternBits.compQuery recordContext) (SignPatternBits.compQuery_FP recordContext_FP)
  have S : SpaceFunction (singleAccess P A).polynomialCoefficient := A.evaluator.precompose testQuery testQuery_FP
  exact FilteredSignProductBits.evaluator (filterAccess P) ((recordAccess P).append (singleAccess P A))
    (filter_controls h) (SignPatternBits.append_controls (records_controls h) (single_controls h A)) hs H Q
    (SignPatternBits.appendCoefficient_evaluator (records_controls h) R S)

theorem raw_bound (P : Readers) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P (origin z) := by
  have H := FilteredSignProductBits.abs_le_count (filter P) (family P T) z
  rw [SignPatternBits.rootCount_eq_card, filter_roots, BoundedCriticalSampleLabels.rootSet_card] at H
  exact H.trans (BoundedFullCriticalSamples.finite_samples P (origin z)).2

theorem raw_packet (P : Readers) (T : Test) (c d r : List Bool) :
    (rawMoment P T (pair (pair c d) r) : ℚ) = ∑ x : BoundedCriticalSampleRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (BoundedCriticalSampleRecords.recordSlots P (pair c r))
        (BoundedCriticalSampleRecords.width P c)
        (fun i => (BoundedCriticalSampleThom.signature P c x i : ℚ)) r * (sign T (pair c d) x.val : ℚ) := by
  rw [rawMoment, FilteredSignProductBits.value, filter_roots]
  simp only [family, SignPatternBits.Family.append, records, single, SignPatternBits.Family.comp,
    recordContext, origin, pairFst_pair, pairSnd_pair, BoundedCriticalSampleRecords.family,
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
  exact BoundedCriticalSampleRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

def leftQuery (q : List Bool) : List Bool := pair (origin q) (pairFst (pairSnd q))
def rightQuery (q : List Bool) : List Bool := pair (origin q) (pairSnd (pairSnd q))
theorem leftQuery_FP : leftQuery ∈ FP := mem_FP_pair origin_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem rightQuery_FP : rightQuery ∈ FP := mem_FP_pair origin_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def source (P : Readers) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedCriticalSampleBasisMoments.record P (leftQuery q) ++ BoundedCriticalSampleBasisMoments.record P (rightQuery q))

theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := BoundedCriticalSampleBasisMoments.record_evaluator h ha
  have L := E.precompose leftQuery leftQuery_FP
  have R := E.precompose rightQuery rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose BoundedCriticalSampleTestMoments.finish BoundedCriticalSampleTestMoments.finish_FP).congr
    (funext fun q => by simp only [source, BoundedCriticalSampleTestMoments.finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h ha).chain (raw_evaluator h A ha)

theorem moment_bound (P : Readers) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P (origin q) := by
  simpa only [moment, source, origin, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Readers) (T : Test) (c d : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (moment P T (pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedCriticalSampleRecordSpan.Root P c, BoundedCriticalSampleRankBasis.selected P c i x *
        BoundedCriticalSampleRankBasis.selected P c j x * (sign T (pair c d) x.val : ℚ) := by
  let a := BoundedCriticalSampleRootHash.record P c i
  let b := BoundedCriticalSampleRootHash.record P c j
  have ha : a.length = BoundedCriticalSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedCriticalSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair (pair c d) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      pair (pair c d) (a ++ b) := by
    simp only [source, leftQuery, rightQuery, origin, pairFst_pair, pairSnd_pair, BoundedCriticalSampleBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedCriticalSampleRecords.recordSlots P (pair c (a ++ b)) =
      BoundedCriticalSampleRecords.slots P c + BoundedCriticalSampleRecords.slots P c := by
    simp only [BoundedCriticalSampleRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedCriticalSampleRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedCriticalSampleRecords.width_pos P c)
  rw [hc]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedCriticalSampleBasisMoments.selected_value, BoundedCriticalSampleBasisMoments.selected_value]

end LeanCanny.Encoding.BoundedCriticalSampleIndexedMoments

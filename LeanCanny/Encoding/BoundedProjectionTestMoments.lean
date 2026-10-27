/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionBasisMoments
public import LeanCanny.Encoding.BoundedProjectionBasisGram

/-! # Native selected-basis moments weighted by an arbitrary polynomial sign

Only the test polynomial's modular coefficients and binary degree and mass
bounds are supplied. A product Tarski query computes the weighted moments;
neither signs at individual roots nor a moment oracle are inputs.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open Brackets MatrixPower
open scoped Classical BigOperators
attribute [local irreducible] BoundedCriticalProjection.polynomial BoundedProjectionRootCount.coefficient
  BoundedProjectionThom.value BoundedProjectionRecords.coefficient

structure Test where
  polynomial : List Bool → ℤ[X]
  degree : List Bool → ℕ
  mass : List Bool → ℕ
  polynomial_degree : ∀ c, (polynomial c).natDegree ≤ degree c
  polynomial_mass : ∀ c, coefficientMass (polynomial c) ≤ 2 ^ mass c

structure Test.Access (T : Test) where
  degree_binary : BinaryFn T.degree
  mass_binary : BinaryFn T.mass
  coefficient : List Bool → List Bool
  coefficient_eq : ∀ c k m, 0 < m → coefficient
    (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((T.polynomial c).coeff k) m
  evaluator : SpaceFunction coefficient

noncomputable def sign (T : Test) (c : List Bool) (x : ℝ) : SignType :=
  SignType.sign (((T.polynomial c).map (Int.castRingHom ℝ)).eval x)

noncomputable def family (P : Readers) (T : Test) : SignQueryBits.Family where
  root z := BoundedCriticalProjection.polynomial P (pairFst z)
  polynomial z i := if i < BoundedProjectionRecords.recordSlots P z then
    BoundedProjectionRecords.polynomial P z i else T.polynomial (pairFst z)
  exponent _ _ := 1
  count z := BinaryNatCode.encode (BoundedProjectionRecords.recordSlots P z + 1)
  rootDegree z := BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z))
  degree z := BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst z) + T.degree (pairFst z))
  rootMass z := BinaryNatCode.encode (BoundedProjectionRootCount.massExponent P (pairFst z))
  mass z := BinaryNatCode.encode (BoundedProjectionThom.massExponent P (pairFst z) + T.mass (pairFst z))
  rootDegree_pos z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact pow_pos (by decide) _
  root_degree z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedCriticalProjection.polynomial_degree P (pairFst z)
  root_mass z := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact BoundedProjectionRootCount.mass_bound P (pairFst z)
  polynomial_degree z i _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    split_ifs with hi
    · have H := (BoundedProjectionRecords.family P).polynomial_degree z i
        (by simpa only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
      exact H.trans (by simp only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
    · exact (T.polynomial_degree _).trans (Nat.le_add_left _ _)
  polynomial_mass z i _ := by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    split_ifs with hi
    · have H := (BoundedProjectionRecords.family P).polynomial_mass z i
        (by simpa only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
      apply H.trans
      apply Nat.pow_le_pow_right (by decide)
      simp only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]
      omega
    · exact (T.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))

theorem controls {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access) : SignQueryBits.ControlsPolyTime (family P T) := by
  have hC := bits_mem_FP ((BoundedProjectionRecords.recordSlots_unary h).add (UnaryFn.const 1))
  have hrD : BinaryFn (fun z => BoundedProjectionRootCount.degree P (pairFst z)) :=
    (BoundedProjectionRootCount.degree_binary h).comp pairFst_mem_FP
  have hrB : BinaryFn (fun z => BoundedProjectionRootCount.massExponent P (pairFst z)) :=
    (BoundedProjectionRootCount.massExponent_binary h).comp pairFst_mem_FP
  have htB : BinaryFn (fun z => BoundedProjectionThom.massExponent P (pairFst z)) :=
    (BoundedProjectionThom.massExponent_binary h).comp pairFst_mem_FP
  have hTD : BinaryFn (fun z => T.degree (pairFst z)) := A.degree_binary.comp pairFst_mem_FP
  have hTB : BinaryFn (fun z => T.mass (pairFst z)) := A.mass_binary.comp pairFst_mem_FP
  have hD : BinaryFn (fun z => BoundedProjectionRootCount.degree P (pairFst z) + T.degree (pairFst z)) :=
    hrD.add hTD
  have hB : BinaryFn (fun z => BoundedProjectionThom.massExponent P (pairFst z) + T.mass (pairFst z)) :=
    htB.add hTB
  exact ⟨hC, hrD.bits_mem_FP, hD.bits_mem_FP, hrB.bits_mem_FP, hB.bits_mem_FP⟩

def testQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (BoundedProjectionThom.original q)) (BoundedProjectionThom.index q)) (pairSnd q)
theorem testQuery_FP : testQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp BoundedProjectionThom.original_FP pairFst_mem_FP) BoundedProjectionThom.index_FP) pairSnd_mem_FP

noncomputable def useRecord (P : Readers) (q : List Bool) : Prop :=
  Nat.fromBitsLE (BoundedProjectionThom.order q) < BoundedProjectionRecords.recordSlots P (BoundedProjectionThom.original q)
noncomputable instance (P : Readers) (q : List Bool) : Decidable (useRecord P q) := inferInstanceAs (Decidable (_ < _))
theorem useRecord_pred {P : Readers} (h : P.PolyTime) : FPPred (useRecord P) :=
  (BinaryFn.fromBits BoundedProjectionThom.order_FP).lt
    (BinaryFn.ofUnary ((BoundedProjectionRecords.recordSlots_unary h).comp BoundedProjectionThom.original_FP))

noncomputable def coefficient (P : Readers) {T : Test} (A : T.Access) (q : List Bool) : List Bool :=
  if useRecord P q then BoundedProjectionRecords.coefficient P q else A.coefficient (testQuery q)
theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P A) := by
  have E := SpaceFunction.branch _ (useRecord_pred h).flag_mem_FP (BoundedProjectionRecords.coefficient_evaluator h ha)
    (A.evaluator.precompose testQuery testQuery_FP)
  exact E.congr (funext fun q => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

noncomputable def access (P : Readers) {T : Test} (A : T.Access) : SignQueryBits.Access (family P T) where
  rootCoefficient := (BoundedProjectionRecords.access P).rootCoefficient
  polynomialCoefficient := coefficient P A
  exponent _ := [true]
  root_eq := (BoundedProjectionRecords.access P).root_eq
  polynomial_eq z i _ k m hm := by
    have hi : useRecord P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
        (BinaryNatCode.encode (m - 1))) ↔ i < BoundedProjectionRecords.recordSlots P z := by
      simp only [useRecord, BoundedProjectionThom.original, BoundedProjectionThom.order,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [coefficient, hi, family]
    by_cases hlt : i < BoundedProjectionRecords.recordSlots P z
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (BoundedProjectionRecords.access P).polynomial_eq z i
        (by simpa only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hlt) k m hm
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      simp only [testQuery, BoundedProjectionThom.original, BoundedProjectionThom.index, pairFst_pair, pairSnd_pair]
      exact A.coefficient_eq (pairFst z) k m hm
  exponent_eq _ _ _ := rfl

noncomputable def rawMoment (P : Readers) (T : Test) (z : List Bool) : ℤ := (family P T).value z
attribute [local irreducible] coefficient
theorem raw_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) := by
  have H := (BoundedProjectionRootCount.coefficient_evaluator h ha).precompose
    SignPatternBits.sourceQuery SignPatternBits.sourceQuery_mem_FP
  have Q := coefficient_evaluator h A ha
  have E := SignQueryBits.evaluator (access P A) (controls h A) (constFn_mem_FP [true]) H Q
  exact E

theorem raw_bound (P : Readers) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst z) := by
  have H := RootSignQueries.tarskiQuery_bounds (((family P T).root z).map (Int.castRingHom ℝ))
    (((family P T).product z).map (Int.castRingHom ℝ))
  have hD : ((BoundedCriticalProjection.polynomial P (pairFst z)).map (Int.castRingHom ℝ)).natDegree ≤
      2 ^ BoundedCriticalProjection.labelWidth P (pairFst z) :=
    Polynomial.natDegree_map_le.trans (BoundedCriticalProjection.polynomial_degree P (pairFst z))
  change -((((BoundedCriticalProjection.polynomial P (pairFst z)).map (Int.castRingHom ℝ)).natDegree : ℤ)) ≤ rawMoment P T z ∧
    rawMoment P T z ≤ (((BoundedCriticalProjection.polynomial P (pairFst z)).map (Int.castRingHom ℝ)).natDegree : ℤ) at H
  omega

theorem raw_packet (P : Readers) (T : Test) (c r : List Bool) :
    (rawMoment P T (pair c r) : ℚ) = ∑ x : BoundedProjectionRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (BoundedProjectionRecords.recordSlots P (pair c r))
        (BoundedProjectionRecords.width P c)
        (fun i => (BoundedProjectionMoments.signature P c x i : ℚ)) r * (sign T c x.val : ℚ) := by
  rw [rawMoment, SignQueryBits.Family.value_eq_sum]
  simp only [family, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    show (1 : Fin 3).val = 1 from rfl, pow_one, algebraMap_int_eq]
  rw [Int.cast_sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_range_succ]
  simp only [lt_self_iff_false, ite_false, Int.cast_mul, Int.cast_prod, SignType.intCast_cast]
  change (∏ i ∈ Finset.range _, _) * (sign T c x.val : ℚ) = _
  congr 1
  unfold SparseFeatureRecords.value
  apply Finset.prod_congr rfl
  intro i hi
  rw [ite_eq_left (Finset.mem_range.mp hi)]
  exact BoundedProjectionRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

noncomputable def source (P : Readers) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedProjectionBasisMoments.record P (BoundedProjectionBasisGram.leftQuery q) ++
    BoundedProjectionBasisMoments.record P (BoundedProjectionBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := BoundedProjectionBasisMoments.record_evaluator h ha
  have L := E.precompose BoundedProjectionBasisGram.leftQuery BoundedProjectionBasisGram.leftQuery_FP
  have R := E.precompose BoundedProjectionBasisGram.rightQuery BoundedProjectionBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h ha).chain (raw_evaluator h A ha)

theorem moment_bound (P : Readers) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Readers) (T : Test) (c : List Bool) (i j : Fin (BoundedProjectionRootCount.count P c)) :
    (moment P T (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedProjectionRecordSpan.Root P c, BoundedProjectionRankBasis.selected P c i x *
        BoundedProjectionRankBasis.selected P c j x * (sign T c x.val : ℚ) := by
  let a := BoundedProjectionRootHash.record P c i
  let b := BoundedProjectionRootHash.record P c j
  have ha : a.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, BoundedProjectionBasisGram.leftQuery, BoundedProjectionBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, BoundedProjectionBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedProjectionRecords.recordSlots P (pair c (a ++ b)) =
      BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c := by
    simp only [BoundedProjectionRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedProjectionRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedProjectionRecords.width_pos P c)
  rw [hc]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedProjectionBasisMoments.selected_value, BoundedProjectionBasisMoments.selected_value]

end LeanCanny.Encoding.BoundedProjectionTestMoments

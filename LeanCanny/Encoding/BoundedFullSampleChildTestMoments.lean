/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildBasisMoments
public import LeanCanny.Encoding.BoundedFullSampleChildBasisGram
public import LeanCanny.Algebra.DyadicConstantCoefficient

/-! # Native selected-basis moments weighted by an arbitrary polynomial sign

Only the test polynomial's modular coefficients and binary degree and mass
bounds are supplied. A filtered product query computes the weighted moments;
neither signs at individual roots nor a moment oracle are inputs.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open Brackets MatrixPower
open BoundedFullSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count
attribute [local irreducible] BoundedFullSampleChildCoordinates.parameter PrimitivePairBits.coefficient
  BoundedFullSampleChildThom.value BoundedFullSampleChildRecords.coefficient

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

noncomputable def Test.Access.ofPrimitive {T : Test} (hD : BinaryFn T.degree) (hB : BinaryFn T.mass)
    (E : SpaceFunction (PrimitivePairBits.coefficient T.polynomial)) : T.Access where
  degree_binary := hD
  mass_binary := hB
  coefficient := PrimitivePairBits.coefficient T.polynomial
  evaluator := E
  coefficient_eq c k m hm := by
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue,
      IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])
      (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

noncomputable def sign (T : Test) (c : List Bool) (x : ℝ) : SignType :=
  SignType.sign (((T.polynomial c).map (Int.castRingHom ℝ)).eval x)

noncomputable def family (P : Inputs) (T : Test) : SignPatternBits.Family :=
  { BoundedFullSampleChildRecords.family P with
    polynomial := fun z i => if i < BoundedFullSampleChildRecords.recordSlots P z then
      BoundedFullSampleChildRecords.polynomial P z i else T.polynomial (pairFst z)
    count := fun z => BinaryNatCode.encode (BoundedFullSampleChildRecords.recordSlots P z + 1)
    degree := fun z => BinaryNatCode.encode (BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z))
    mass := fun z => BinaryNatCode.encode (BoundedFullSampleChildThom.massExponent P (pairFst z) + T.mass (pairFst z))
    polynomial_degree := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (BoundedFullSampleChildRecords.family P).polynomial_degree z i
          (by simpa only [BoundedFullSampleChildRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        exact H.trans (by simp only [BoundedFullSampleChildRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
      · exact (T.polynomial_degree _).trans (Nat.le_add_left _ _)
    polynomial_mass := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (BoundedFullSampleChildRecords.family P).polynomial_mass z i
          (by simpa only [BoundedFullSampleChildRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        apply H.trans
        apply Nat.pow_le_pow_right (by decide)
        simp only [BoundedFullSampleChildRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      · exact (T.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)) }

attribute [local irreducible] BoundedFullSampleChildThom.massExponent

theorem controls {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SignPatternBits.ControlsPolyTime (family P T) := by
  have hrD : BinaryFn (fun z => BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z)) :=
    (BoundedFullSampleChildCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hrB : BinaryFn (fun z => BoundedFullSampleChildThom.massExponent P (pairFst z)) :=
    (BoundedFullSampleChildThom.massExponent_binary h).comp pairFst_mem_FP
  have htD : BinaryFn (fun z => T.degree (pairFst z)) := A.degree_binary.comp pairFst_mem_FP
  have htB : BinaryFn (fun z => T.mass (pairFst z)) := A.mass_binary.comp pairFst_mem_FP
  have hD : BinaryFn (fun z => BoundedFullSampleChildCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z)) :=
    hrD.add htD
  have hB : BinaryFn (fun z => BoundedFullSampleChildThom.massExponent P (pairFst z) + T.mass (pairFst z)) :=
    hrB.add htB
  refine ⟨bits_mem_FP ((BoundedFullSampleChildRecords.recordSlots_unary h).add (UnaryFn.const 1)), ?_,
    (BoundedFullSampleChildRecords.controls h).rootDegree, hD.bits_mem_FP,
    (BoundedFullSampleChildRecords.controls h).rootMass, hB.bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
    (BoundedFullSampleChildRecords.recordSlots_unary h).add (UnaryFn.const 1)

def testQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (BoundedFullSampleChildThom.original q)) (BoundedFullSampleChildThom.index q)) (pairSnd q)
theorem testQuery_FP : testQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp BoundedFullSampleChildThom.original_FP pairFst_mem_FP) BoundedFullSampleChildThom.index_FP) pairSnd_mem_FP

noncomputable def useRecord (P : Inputs) (q : List Bool) : Prop :=
  Nat.fromBitsLE (BoundedFullSampleChildThom.order q) < BoundedFullSampleChildRecords.recordSlots P (BoundedFullSampleChildThom.original q)
noncomputable instance (P : Inputs) (q : List Bool) : Decidable (useRecord P q) := inferInstanceAs (Decidable (_ < _))
theorem useRecord_pred {P : Inputs} (h : P.PolyTime) : FPPred (useRecord P) :=
  (BinaryFn.fromBits BoundedFullSampleChildThom.order_FP).lt
    (BinaryFn.ofUnary ((BoundedFullSampleChildRecords.recordSlots_unary h).comp BoundedFullSampleChildThom.original_FP))

noncomputable def coefficient (P : Inputs) {T : Test} (A : T.Access) (q : List Bool) : List Bool :=
  if useRecord P q then BoundedFullSampleChildRecords.coefficient P q else A.coefficient (testQuery q)
theorem coefficient_evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) : SpaceFunction (coefficient P A) := by
  have E := SpaceFunction.branch _ (useRecord_pred h).flag_mem_FP (BoundedFullSampleChildRecords.coefficient_evaluator h)
    (A.evaluator.precompose testQuery testQuery_FP)
  exact E.congr (funext fun q => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

noncomputable def access (P : Inputs) {T : Test} (A : T.Access) : SignPatternBits.Access (family P T) where
  rootCoefficient := (BoundedFullSampleChildRecords.access P).rootCoefficient
  polynomialCoefficient := coefficient P A
  pattern _ := []
  root_eq := (BoundedFullSampleChildRecords.access P).root_eq
  polynomial_eq z i _ k m hm := by
    have hi : useRecord P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
        (BinaryNatCode.encode (m - 1))) ↔ i < BoundedFullSampleChildRecords.recordSlots P z := by
      simp only [useRecord, BoundedFullSampleChildThom.original, BoundedFullSampleChildThom.order,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [coefficient, hi, family]
    by_cases hlt : i < BoundedFullSampleChildRecords.recordSlots P z
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (BoundedFullSampleChildRecords.access P).polynomial_eq z i
        (by simpa only [BoundedFullSampleChildRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hlt) k m hm
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      simp only [testQuery, BoundedFullSampleChildThom.original, BoundedFullSampleChildThom.index, pairFst_pair, pairSnd_pair]
      exact A.coefficient_eq (pairFst z) k m hm
  pattern_eq _ _ := rfl

noncomputable def rawMoment (P : Inputs) (T : Test) (z : List Bool) : ℤ :=
  BoundedFullSampleChildReindexedQueries.moment P pairFst (family P T) z
attribute [local irreducible] coefficient

theorem raw_evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) :=
  BoundedFullSampleChildReindexedQueries.evaluator h pairFst_mem_FP (access P A) (controls h A) (coefficient_evaluator h A)

theorem raw_bound (P : Inputs) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ BoundedFullSampleChildThom.labelWidth P (pairFst z) :=
  (BoundedFullSampleChildReindexedQueries.moment_bound P pairFst (family P T) z).trans
    (by simpa only [BoundedFullSampleChildThom.labelWidth] using BoundedFullSampleChildRegularCount.count_le P (pairFst z))

theorem raw_packet (P : Inputs) (T : Test) (c r : List Bool) :
    (rawMoment P T (pair c r) : ℚ) = ∑ x : BoundedFullSampleChildRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (BoundedFullSampleChildRecords.recordSlots P (pair c r))
        (BoundedFullSampleChildRecords.width P c)
        (fun i => (BoundedFullSampleChildThom.signature P c x i : ℚ)) r * (sign T c x.val : ℚ) := by
  rw [rawMoment, BoundedFullSampleChildReindexedQueries.moment]
  simp only [BoundedFullSampleChildQueries.product]
  simp only [family, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    algebraMap_int_eq]
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
  exact BoundedFullSampleChildRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

noncomputable def source (P : Inputs) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedFullSampleChildBasisMoments.record P (BoundedFullSampleChildBasisGram.leftQuery q) ++
    BoundedFullSampleChildBasisMoments.record P (BoundedFullSampleChildBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (source P) := by
  have E := BoundedFullSampleChildBasisMoments.record_evaluator h
  have L := E.precompose BoundedFullSampleChildBasisGram.leftQuery BoundedFullSampleChildBasisGram.leftQuery_FP
  have R := E.precompose BoundedFullSampleChildBasisGram.rightQuery BoundedFullSampleChildBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Inputs) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Inputs} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h).chain (raw_evaluator h A)

theorem moment_bound (P : Inputs) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedFullSampleChildThom.labelWidth P (pairFst q) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Inputs) (T : Test) (c : List Bool) (i j : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (moment P T (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedFullSampleChildRecordSpan.Root P c, BoundedFullSampleChildRankBasis.selected P c i x *
        BoundedFullSampleChildRankBasis.selected P c j x * (sign T c x.val : ℚ) := by
  let a := BoundedFullSampleChildRootHash.record P c i
  let b := BoundedFullSampleChildRootHash.record P c j
  have ha : a.length = BoundedFullSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedFullSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, BoundedFullSampleChildBasisGram.leftQuery, BoundedFullSampleChildBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, BoundedFullSampleChildBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : BoundedFullSampleChildRecords.recordSlots P (pair c (a ++ b)) =
      BoundedFullSampleChildRecords.slots P c + BoundedFullSampleChildRecords.slots P c := by
    simp only [BoundedFullSampleChildRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, BoundedFullSampleChildRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (BoundedFullSampleChildRecords.width_pos P c)
  rw [hc]
  have ha' : a.length = BoundedFullSampleChildRecords.slots P c * BoundedFullSampleChildRecords.width P c := by
    simpa only [BoundedFullSampleChildRecords.length] using ha
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha',
    BoundedFullSampleChildBasisMoments.selected_value, BoundedFullSampleChildBasisMoments.selected_value]

noncomputable def unit : Test where
  polynomial _ := 1
  degree _ := 0
  mass _ := 0
  polynomial_degree _ := by simp only [natDegree_one, Nat.zero_le]
  polynomial_mass _ := by simp only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one, pow_zero, le_refl]

noncomputable def unitAccess : unit.Access where
  degree_binary := BinaryFn.const 0
  mass_binary := BinaryFn.const 0
  coefficient := PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X]))
  evaluator := DyadicConstantBits.oneCoefficientEvaluator
  coefficient_eq c k m hm := by
    simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.coefficientResidue,
      IntegerTarskiSeedBits.integerResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [RationalSubstitution.IntegerBits.selectedDegree,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [RationalSubstitution.IntegerBits.mValue, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

theorem sign_unit (c : List Bool) (x : ℝ) : sign unit c x = .pos := by
  simp only [sign, unit, Polynomial.map_one, Polynomial.eval_one, sign_one]
  rfl

end LeanCanny.Encoding.BoundedFullSampleChildTestMoments

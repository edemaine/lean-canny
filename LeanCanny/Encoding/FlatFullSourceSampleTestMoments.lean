/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleBasisMoments
public import LeanCanny.Encoding.FlatFullSourceSampleBasisGram
public import LeanCanny.Algebra.DyadicConstantCoefficient

/-! # Native selected-basis moments weighted by an arbitrary polynomial sign

Only the test polynomial's modular coefficients and binary degree and mass
bounds are supplied. A filtered product query computes the weighted moments;
neither signs at individual roots nor a moment oracle are inputs.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open Brackets MatrixPower
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count
attribute [local irreducible] FlatFullSourceSampleCoordinates.parameter PrimitivePairBits.coefficient
  FlatFullSourceSampleThom.value FlatFullSourceSampleRecords.coefficient

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
  { FlatFullSourceSampleRecords.family P with
    polynomial := fun z i => if i < FlatFullSourceSampleRecords.recordSlots P z then
      FlatFullSourceSampleRecords.polynomial P z i else T.polynomial (pairFst z)
    count := fun z => BinaryNatCode.encode (FlatFullSourceSampleRecords.recordSlots P z + 1)
    degree := fun z => BinaryNatCode.encode (FlatFullSourceSampleCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z))
    mass := fun z => BinaryNatCode.encode (FlatFullSourceSampleThom.massExponent P (pairFst z) + T.mass (pairFst z))
    polynomial_degree := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (FlatFullSourceSampleRecords.family P).polynomial_degree z i
          (by simpa only [FlatFullSourceSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        exact H.trans (by simp only [FlatFullSourceSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
      · exact (T.polynomial_degree _).trans (Nat.le_add_left _ _)
    polynomial_mass := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (FlatFullSourceSampleRecords.family P).polynomial_mass z i
          (by simpa only [FlatFullSourceSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        apply H.trans
        apply Nat.pow_le_pow_right (by decide)
        simp only [FlatFullSourceSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      · exact (T.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)) }

attribute [local irreducible] FlatFullSourceSampleThom.massExponent

theorem controls {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SignPatternBits.ControlsPolyTime (family P T) := by
  have hrD : BinaryFn (fun z => FlatFullSourceSampleCoordinates.parameterDegree P (pairFst z)) :=
    (FlatFullSourceSampleCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hrB : BinaryFn (fun z => FlatFullSourceSampleThom.massExponent P (pairFst z)) :=
    (FlatFullSourceSampleThom.massExponent_binary h).comp pairFst_mem_FP
  have htD : BinaryFn (fun z => T.degree (pairFst z)) := A.degree_binary.comp pairFst_mem_FP
  have htB : BinaryFn (fun z => T.mass (pairFst z)) := A.mass_binary.comp pairFst_mem_FP
  have hD : BinaryFn (fun z => FlatFullSourceSampleCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z)) :=
    hrD.add htD
  have hB : BinaryFn (fun z => FlatFullSourceSampleThom.massExponent P (pairFst z) + T.mass (pairFst z)) :=
    hrB.add htB
  refine ⟨bits_mem_FP ((FlatFullSourceSampleRecords.recordSlots_unary h).add (UnaryFn.const 1)), ?_,
    (FlatFullSourceSampleRecords.controls h).rootDegree, hD.bits_mem_FP,
    (FlatFullSourceSampleRecords.controls h).rootMass, hB.bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
    (FlatFullSourceSampleRecords.recordSlots_unary h).add (UnaryFn.const 1)

def testQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (FlatFullSourceSampleThom.original q)) (FlatFullSourceSampleThom.index q)) (pairSnd q)
theorem testQuery_FP : testQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp FlatFullSourceSampleThom.original_FP pairFst_mem_FP) FlatFullSourceSampleThom.index_FP) pairSnd_mem_FP

noncomputable def useRecord (P : Inputs) (q : List Bool) : Prop :=
  Nat.fromBitsLE (FlatFullSourceSampleThom.order q) < FlatFullSourceSampleRecords.recordSlots P (FlatFullSourceSampleThom.original q)
noncomputable instance (P : Inputs) (q : List Bool) : Decidable (useRecord P q) := inferInstanceAs (Decidable (_ < _))
theorem useRecord_pred {P : Inputs} (h : P.Access) : FPPred (useRecord P) :=
  (BinaryFn.fromBits FlatFullSourceSampleThom.order_FP).lt
    (BinaryFn.ofUnary ((FlatFullSourceSampleRecords.recordSlots_unary h).comp FlatFullSourceSampleThom.original_FP))

noncomputable def coefficient (P : Inputs) {T : Test} (A : T.Access) (q : List Bool) : List Bool :=
  if useRecord P q then FlatFullSourceSampleRecords.coefficient P q else A.coefficient (testQuery q)
theorem coefficient_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) : SpaceFunction (coefficient P A) := by
  have E := SpaceFunction.branch _ (useRecord_pred h).flag_mem_FP (FlatFullSourceSampleRecords.coefficient_evaluator h)
    (A.evaluator.precompose testQuery testQuery_FP)
  exact E.congr (funext fun q => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

noncomputable def access (P : Inputs) {T : Test} (A : T.Access) : SignPatternBits.Access (family P T) where
  rootCoefficient := (FlatFullSourceSampleRecords.access P).rootCoefficient
  polynomialCoefficient := coefficient P A
  pattern _ := []
  root_eq := (FlatFullSourceSampleRecords.access P).root_eq
  polynomial_eq z i _ k m hm := by
    have hi : useRecord P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
        (BinaryNatCode.encode (m - 1))) ↔ i < FlatFullSourceSampleRecords.recordSlots P z := by
      simp only [useRecord, FlatFullSourceSampleThom.original, FlatFullSourceSampleThom.order,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [coefficient, hi, family]
    by_cases hlt : i < FlatFullSourceSampleRecords.recordSlots P z
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (FlatFullSourceSampleRecords.access P).polynomial_eq z i
        (by simpa only [FlatFullSourceSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hlt) k m hm
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      simp only [testQuery, FlatFullSourceSampleThom.original, FlatFullSourceSampleThom.index, pairFst_pair, pairSnd_pair]
      exact A.coefficient_eq (pairFst z) k m hm
  pattern_eq _ _ := rfl

noncomputable def rawMoment (P : Inputs) (T : Test) (z : List Bool) : ℤ :=
  FlatFullSourceSampleReindexedQueries.moment P pairFst (family P T) z
attribute [local irreducible] coefficient

theorem raw_evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) :=
  FlatFullSourceSampleReindexedQueries.evaluator h pairFst_mem_FP (access P A) (controls h A) (coefficient_evaluator h A)

theorem raw_bound (P : Inputs) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst z) :=
  (FlatFullSourceSampleReindexedQueries.moment_bound P pairFst (family P T) z).trans
    (by simpa only [FlatFullSourceSampleThom.labelWidth] using FlatFullSourceSampleRegularCount.count_le P (pairFst z))

theorem raw_packet (P : Inputs) (T : Test) (c r : List Bool) :
    (rawMoment P T (pair c r) : ℚ) = ∑ x : FlatFullSourceSampleRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (FlatFullSourceSampleRecords.recordSlots P (pair c r))
        (FlatFullSourceSampleRecords.width P c)
        (fun i => (FlatFullSourceSampleThom.signature P c x i : ℚ)) r * (sign T c x.val : ℚ) := by
  rw [rawMoment, FlatFullSourceSampleReindexedQueries.moment]
  simp only [FlatFullSourceSampleQueries.product]
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
  exact FlatFullSourceSampleRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

noncomputable def source (P : Inputs) (q : List Bool) : List Bool := pair (pairFst q)
  (FlatFullSourceSampleBasisMoments.record P (FlatFullSourceSampleBasisGram.leftQuery q) ++
    FlatFullSourceSampleBasisMoments.record P (FlatFullSourceSampleBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Inputs} (h : P.Access) : SpaceFunction (source P) := by
  have E := FlatFullSourceSampleBasisMoments.record_evaluator h
  have L := E.precompose FlatFullSourceSampleBasisGram.leftQuery FlatFullSourceSampleBasisGram.leftQuery_FP
  have R := E.precompose FlatFullSourceSampleBasisGram.rightQuery FlatFullSourceSampleBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Inputs) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Inputs} (h : P.Access) {T : Test} (A : T.Access) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h).chain (raw_evaluator h A)

theorem moment_bound (P : Inputs) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ FlatFullSourceSampleThom.labelWidth P (pairFst q) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Inputs) (T : Test) (c : List Bool) (i j : Fin (FlatFullSourceSampleRegularCount.count P c)) :
    (moment P T (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : FlatFullSourceSampleRecordSpan.Root P c, FlatFullSourceSampleRankBasis.selected P c i x *
        FlatFullSourceSampleRankBasis.selected P c j x * (sign T c x.val : ℚ) := by
  let a := FlatFullSourceSampleRootHash.record P c i
  let b := FlatFullSourceSampleRootHash.record P c j
  have ha : a.length = FlatFullSourceSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = FlatFullSourceSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, FlatFullSourceSampleBasisGram.leftQuery, FlatFullSourceSampleBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, FlatFullSourceSampleBasisMoments.record_packet]
    rfl
  rw [moment, hs, raw_packet]
  have hc : FlatFullSourceSampleRecords.recordSlots P (pair c (a ++ b)) =
      FlatFullSourceSampleRecords.slots P c + FlatFullSourceSampleRecords.slots P c := by
    simp only [FlatFullSourceSampleRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, FlatFullSourceSampleRecords.length, ← Nat.add_mul]
    exact Nat.mul_div_cancel _ (FlatFullSourceSampleRecords.width_pos P c)
  rw [hc]
  have ha' : a.length = FlatFullSourceSampleRecords.slots P c * FlatFullSourceSampleRecords.width P c := by
    simpa only [FlatFullSourceSampleRecords.length] using ha
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ a b ha',
    FlatFullSourceSampleBasisMoments.selected_value, FlatFullSourceSampleBasisMoments.selected_value]

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

end LeanCanny.Encoding.FlatFullSourceSampleTestMoments

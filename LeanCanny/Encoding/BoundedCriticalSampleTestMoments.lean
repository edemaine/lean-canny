/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBasisMoments
public import LeanCanny.Encoding.BoundedCriticalSampleBasisGram
public import LeanCanny.Algebra.DyadicConstantCoefficient

/-! # Native selected-basis moments weighted by an arbitrary polynomial sign

Only the test polynomial's modular coefficients and binary degree and mass
bounds are supplied. A filtered product query computes the weighted moments;
neither signs at individual roots nor a moment oracle are inputs.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTestMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open Brackets MatrixPower
open scoped Classical BigOperators
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter PrimitivePairBits.coefficient
  BoundedCriticalSampleThom.value BoundedCriticalSampleRecords.coefficient
set_option backward.isDefEq.respectTransparency false

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

noncomputable def family (P : Readers) (T : Test) : SignPatternBits.Family :=
  { BoundedCriticalSampleRecords.family P with
    polynomial := fun z i => if i < BoundedCriticalSampleRecords.recordSlots P z then
      BoundedCriticalSampleRecords.polynomial P z i else T.polynomial (pairFst z)
    count := fun z => BinaryNatCode.encode (BoundedCriticalSampleRecords.recordSlots P z + 1)
    degree := fun z => BinaryNatCode.encode (BoundedCriticalRationalCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z))
    mass := fun z => BinaryNatCode.encode (BoundedCriticalSampleThom.massExponent P (pairFst z) + T.mass (pairFst z))
    polynomial_degree := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (BoundedCriticalSampleRecords.family P).polynomial_degree z i
          (by simpa only [BoundedCriticalSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        exact H.trans (by simp only [BoundedCriticalSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
      · exact (T.polynomial_degree _).trans (Nat.le_add_left _ _)
    polynomial_mass := fun z i _ => by
      simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
      split_ifs with hi
      · have H := (BoundedCriticalSampleRecords.family P).polynomial_mass z i
          (by simpa only [BoundedCriticalSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi)
        apply H.trans
        apply Nat.pow_le_pow_right (by decide)
        simp only [BoundedCriticalSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits]
        omega
      · exact (T.polynomial_mass _).trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)) }

attribute [local irreducible] BoundedCriticalRationalCoordinates.parameterDegree
  BoundedCriticalRationalCoordinates.baseHeight BoundedCriticalSampleThom.massExponent

theorem controls {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access) :
    SignPatternBits.ControlsPolyTime (family P T) := by
  have hrD : BinaryFn (fun z => BoundedCriticalRationalCoordinates.parameterDegree P (pairFst z)) :=
    (BoundedCriticalRationalCoordinates.parameterDegree_binary h).comp pairFst_mem_FP
  have hrB : BinaryFn (fun z => BoundedCriticalSampleThom.massExponent P (pairFst z)) :=
    (BoundedCriticalSampleThom.massExponent_binary h).comp pairFst_mem_FP
  have htD : BinaryFn (fun z => T.degree (pairFst z)) := A.degree_binary.comp pairFst_mem_FP
  have htB : BinaryFn (fun z => T.mass (pairFst z)) := A.mass_binary.comp pairFst_mem_FP
  have hD : BinaryFn (fun z => BoundedCriticalRationalCoordinates.parameterDegree P (pairFst z) + T.degree (pairFst z)) :=
    hrD.add htD
  have hB : BinaryFn (fun z => BoundedCriticalSampleThom.massExponent P (pairFst z) + T.mass (pairFst z)) :=
    hrB.add htB
  refine ⟨bits_mem_FP ((BoundedCriticalSampleRecords.recordSlots_unary h).add (UnaryFn.const 1)), ?_,
    (BoundedCriticalSampleRecords.controls h).rootDegree, hD.bits_mem_FP,
    (BoundedCriticalSampleRecords.controls h).rootMass, hB.bits_mem_FP⟩
  simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
    (BoundedCriticalSampleRecords.recordSlots_unary h).add (UnaryFn.const 1)

def testQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (BoundedCriticalSampleThom.original q)) (BoundedCriticalSampleThom.index q)) (pairSnd q)
theorem testQuery_FP : testQuery ∈ FP := mem_FP_pair
  (mem_FP_pair (mem_FP_comp BoundedCriticalSampleThom.original_FP pairFst_mem_FP) BoundedCriticalSampleThom.index_FP) pairSnd_mem_FP

noncomputable def useRecord (P : Readers) (q : List Bool) : Prop :=
  Nat.fromBitsLE (BoundedCriticalSampleThom.order q) < BoundedCriticalSampleRecords.recordSlots P (BoundedCriticalSampleThom.original q)
noncomputable instance (P : Readers) (q : List Bool) : Decidable (useRecord P q) := inferInstanceAs (Decidable (_ < _))
theorem useRecord_pred {P : Readers} (h : P.PolyTime) : FPPred (useRecord P) :=
  (BinaryFn.fromBits BoundedCriticalSampleThom.order_FP).lt
    (BinaryFn.ofUnary ((BoundedCriticalSampleRecords.recordSlots_unary h).comp BoundedCriticalSampleThom.original_FP))

noncomputable def coefficient (P : Readers) {T : Test} (A : T.Access) (q : List Bool) : List Bool :=
  if useRecord P q then BoundedCriticalSampleRecords.coefficient P q else A.coefficient (testQuery q)
theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P A) := by
  have E := SpaceFunction.branch _ (useRecord_pred h).flag_mem_FP (BoundedCriticalSampleRecords.coefficient_evaluator h ha)
    (A.evaluator.precompose testQuery testQuery_FP)
  exact E.congr (funext fun q => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

noncomputable def access (P : Readers) {T : Test} (A : T.Access) : SignPatternBits.Access (family P T) where
  rootCoefficient := (BoundedCriticalSampleRecords.access P).rootCoefficient
  polynomialCoefficient := coefficient P A
  pattern _ := []
  root_eq := (BoundedCriticalSampleRecords.access P).root_eq
  polynomial_eq z i _ k m hm := by
    have hi : useRecord P (pair (pair z (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
        (BinaryNatCode.encode (m - 1))) ↔ i < BoundedCriticalSampleRecords.recordSlots P z := by
      simp only [useRecord, BoundedCriticalSampleThom.original, BoundedCriticalSampleThom.order,
        pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [coefficient, hi, family]
    by_cases hlt : i < BoundedCriticalSampleRecords.recordSlots P z
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      exact (BoundedCriticalSampleRecords.access P).polynomial_eq z i
        (by simpa only [BoundedCriticalSampleRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hlt) k m hm
    · rw [ite_eq_right hlt, ite_eq_right hlt]
      simp only [testQuery, BoundedCriticalSampleThom.original, BoundedCriticalSampleThom.index, pairFst_pair, pairSnd_pair]
      exact A.coefficient_eq (pairFst z) k m hm
  pattern_eq _ _ := rfl

noncomputable def rawMoment (P : Readers) (T : Test) (z : List Bool) : ℤ :=
  FilteredSignProductBits.value (BoundedCriticalSampleRecords.filter P) (family P T) z
attribute [local irreducible] coefficient
theorem raw_evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (rawMoment P T z)) := by
  have hq := SignPatternBits.compQuery_FP pairFst_mem_FP
  have H : SpaceFunction (BoundedCriticalSampleRecords.filterAccess P).rootCoefficient :=
    (BoundedCriticalRationalCoordinates.parameter_coefficient_evaluator h ha).precompose
      (SignPatternBits.compQuery pairFst) hq
  have Q : SpaceFunction (BoundedCriticalSampleRecords.filterAccess P).polynomialCoefficient :=
    ((BoundedCriticalFilterCoefficients.evaluator h ha).precompose
      BoundedCriticalSampleCount.filterQuery BoundedCriticalSampleCount.filterQuery_FP).precompose
        (SignPatternBits.compQuery pairFst) hq
  have hs : (BoundedCriticalSampleRecords.filterAccess P).pattern ∈ FP := by
    change ((BoundedCriticalSampleCount.access P).pattern ∘ SignPatternBits.compPattern pairFst) ∈ FP
    exact mem_FP_comp (SignPatternBits.compPattern_FP pairFst_mem_FP) (constFn_mem_FP [])
  exact FilteredSignProductBits.evaluator (BoundedCriticalSampleRecords.filterAccess P) (access P A)
    (BoundedCriticalSampleRecords.filter_controls h) (controls h A) hs H Q (coefficient_evaluator h A ha)

theorem raw_bound (P : Readers) (T : Test) (z : List Bool) :
    (rawMoment P T z).natAbs ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P (pairFst z) := by
  have H := FilteredSignProductBits.abs_le_count (BoundedCriticalSampleRecords.filter P) (family P T) z
  rw [SignPatternBits.rootCount_eq_card, BoundedCriticalSampleRecords.acceptedRoots_eq,
    BoundedCriticalSampleLabels.rootSet_card] at H
  exact H.trans (BoundedFullCriticalSamples.finite_samples P (pairFst z)).2

theorem raw_packet (P : Readers) (T : Test) (c r : List Bool) :
    (rawMoment P T (pair c r) : ℚ) = ∑ x : BoundedCriticalSampleRecordSpan.Root P c,
      SparseFeatureRecords.value (Nat.succ_pos _) (BoundedCriticalSampleRecords.recordSlots P (pair c r))
        (BoundedCriticalSampleRecords.width P c)
        (fun i => (BoundedCriticalSampleThom.signature P c x i : ℚ)) r * (sign T c x.val : ℚ) := by
  rw [rawMoment, FilteredSignProductBits.value, BoundedCriticalSampleRecords.acceptedRoots_eq]
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
  exact BoundedCriticalSampleRecordSpan.sign_polynomial P c r i (Finset.mem_range.mp hi) x

noncomputable def source (P : Readers) (q : List Bool) : List Bool := pair (pairFst q)
  (BoundedCriticalSampleBasisMoments.record P (BoundedCriticalSampleBasisGram.leftQuery q) ++
    BoundedCriticalSampleBasisMoments.record P (BoundedCriticalSampleBasisGram.rightQuery q))
def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z)) (pairFst (pairSnd z) ++ pairSnd (pairSnd z))
theorem finish_FP : finish ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  (appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := BoundedCriticalSampleBasisMoments.record_evaluator h ha
  have L := E.precompose BoundedCriticalSampleBasisGram.leftQuery BoundedCriticalSampleBasisGram.leftQuery_FP
  have R := E.precompose BoundedCriticalSampleBasisGram.rightQuery BoundedCriticalSampleBasisGram.rightQuery_FP
  exact ((L.pairOutputs R).withInput.postcompose finish finish_FP).congr
    (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (T : Test) (q : List Bool) : ℤ := rawMoment P T (source P q)
theorem evaluator {P : Readers} (h : P.PolyTime) {T : Test} (A : T.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P T q)) :=
  (source_evaluator h ha).chain (raw_evaluator h A ha)

theorem moment_bound (P : Readers) (T : Test) (q : List Bool) :
    (moment P T q).natAbs ≤ 2 ^ BoundedFullCriticalSamples.labelWidth P (pairFst q) := by
  simpa only [moment, source, pairFst_pair] using raw_bound P T (source P q)

theorem moment_packet (P : Readers) (T : Test) (c : List Bool) (i j : Fin (BoundedCriticalSampleCount.count P c)) :
    (moment P T (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
      ∑ x : BoundedCriticalSampleRecordSpan.Root P c, BoundedCriticalSampleRankBasis.selected P c i x *
        BoundedCriticalSampleRankBasis.selected P c j x * (sign T c x.val : ℚ) := by
  let a := BoundedCriticalSampleRootHash.record P c i
  let b := BoundedCriticalSampleRootHash.record P c j
  have ha : a.length = BoundedCriticalSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedCriticalSampleRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = pair c (a ++ b) := by
    simp only [source, BoundedCriticalSampleBasisGram.leftQuery, BoundedCriticalSampleBasisGram.rightQuery,
      pairFst_pair, pairSnd_pair, BoundedCriticalSampleBasisMoments.record_packet]
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

end LeanCanny.Encoding.BoundedCriticalSampleTestMoments

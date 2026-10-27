/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleTermCoordinates
public import LeanCanny.ETR.BivariateRationalTermReader

/-! # Native rational coordinates for lines through actual samples

The context is `pair source record`. One binary coordinate index selects
the free outer variable. All other coordinates retain the sample parameter;
unused coordinates are zero over one. Both modular readers are constructed
from the original sample-coordinate readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleLineCoordinates
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Brackets
open MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinateDegree
  BoundedCriticalRationalCoordinates.coordinateMass PrimitivePairBits.coefficient

noncomputable def base (P : Readers) (b : Bool) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if b then BoundedCriticalSampleTermCoordinates.numerator P u i else BoundedCriticalSampleTermCoordinates.denominator P u i
noncomputable def freePolynomial (b : Bool) : (ℤ[X])[X] := if b then X else 1
theorem free_coefficient (b : Bool) (j : ℕ) :
    (freePolynomial b).coeff j = if j = (if b then 1 else 0) then 1 else 0 := by
  cases b <;> simp [freePolynomial, coeff_one, coeff_X, eq_comm]
noncomputable def polynomial (P : Readers) (f : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) : (ℤ[X])[X] :=
  if i = f u then freePolynomial b else C (base P b u i)

theorem base_degree (P : Readers) (b : Bool) (u : List Bool) (i : ℕ) :
    (base P b u i).natDegree ≤ BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u) := by
  cases b
  · exact BoundedCriticalSampleTermCoordinates.denominator_degree P u i
  · exact BoundedCriticalSampleTermCoordinates.numerator_degree P u i
theorem base_mass (P : Readers) (b : Bool) (u : List Bool) (i : ℕ) :
    coefficientMass (base P b u i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := by
  cases b
  · exact BoundedCriticalSampleTermCoordinates.denominator_mass P u i
  · exact BoundedCriticalSampleTermCoordinates.numerator_mass P u i

noncomputable def family (P : Readers) (f : List Bool → ℕ) (b : Bool) : BivariateQueryProductBits.Family where
  polynomial := polynomial P f b
  exponent _ _ := 1
  count u := P.dim (pairFst u) + 4
  degree _ := 1
  parameterDegree u := BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u)
  mass u := BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u)
  polynomial_degree u i := by
    unfold polynomial
    split_ifs
    · cases b <;> simp [freePolynomial]
    · simp only [natDegree_C, Nat.zero_le]
  coefficient_degree u i j := by
    unfold polynomial
    split_ifs
    · rw [free_coefficient]
      split_ifs <;> simp only [natDegree_one, natDegree_zero, Nat.zero_le]
    · rw [coeff_C]
      split_ifs
      · exact base_degree P b u i
      · simp only [natDegree_zero, Nat.zero_le]
  coefficient_mass u i j := by
    unfold polynomial
    split_ifs
    · rw [free_coefficient]
      have hp : 1 ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := Nat.one_le_two_pow
      split_ifs <;> simp only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one, coefficientMass_zero] <;> omega
    · rw [coeff_C]
      split_ifs
      · exact base_mass P b u i
      · simp only [coefficientMass_zero, Nat.zero_le]

def source (z : List Bool) : List Bool := pairFst (pairFst (pairFst z))
def index (z : List Bool) : List Bool := pairSnd (pairFst (pairFst z))
def innerWord (z : List Bool) : List Bool := pairFst (pairSnd z)
def outerWord (z : List Bool) : List Bool := pairSnd (pairSnd z)
def modulusWord (z : List Bool) : List Bool := pairSnd (pairFst z)
theorem source_FP : source ∈ FP := by polytime [source]
theorem index_FP : index ∈ FP := by polytime [index]
theorem innerWord_FP : innerWord ∈ FP := by polytime [innerWord]
theorem outerWord_FP : outerWord ∈ FP := by polytime [outerWord]
theorem modulusWord_FP : modulusWord ∈ FP := by polytime [modulusWord]

def baseQuery (z : List Bool) : List Bool := pair (pair (source z)
  (pair (BinaryNat.normalize (index z)) (innerWord z))) (BinaryNat.normalize (modulusWord z))
def oneQuery (z : List Bool) : List Bool := pair (pair (source z) (innerWord z)) (BinaryNat.normalize (modulusWord z))
theorem baseQuery_FP : baseQuery ∈ FP := mem_FP_pair (mem_FP_pair source_FP
  (mem_FP_pair (mem_FP_comp index_FP BinaryNat.normalize_mem_FP) innerWord_FP))
    (mem_FP_comp modulusWord_FP BinaryNat.normalize_mem_FP)
theorem oneQuery_FP : oneQuery ∈ FP := mem_FP_pair (mem_FP_pair source_FP innerWord_FP)
  (mem_FP_comp modulusWord_FP BinaryNat.normalize_mem_FP)

noncomputable def baseCode (P : Readers) (b : Bool) : List Bool → List Bool :=
  if b then BoundedCriticalSampleTermCoordinates.numeratorCode P else BoundedCriticalSampleTermCoordinates.denominatorCode P
theorem baseCode_evaluator {P : Readers} (h : P.PolyTime) (b : Bool)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (baseCode P b) := by
  cases b
  · exact BoundedCriticalSampleTermCoordinates.denominator_evaluator h ha
  · exact BoundedCriticalSampleTermCoordinates.numerator_evaluator h ha

theorem baseCode_packet (P : Readers) (b : Bool) (u : List Bool) (i k m : ℕ) (hm : 0 < m) :
    baseCode P b (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((base P b u i).coeff k : ℤ) : ZMod m) := by
  cases b
  · exact BoundedCriticalSampleTermCoordinates.denominator_packet P u i k m hm
  · exact BoundedCriticalSampleTermCoordinates.numerator_packet P u i k m hm

theorem one_packet (q : List Bool) (k j : ℕ) :
    PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X])) (oneQuery (pair q (pair (BinaryNatCode.encode k) (BinaryNatCode.encode j)))) =
      residueBits ((((1 : ℤ[X]).coeff k : ℤ)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have H := BoundedCriticalSampleTestMoments.unitAccess.coefficient_eq (pairFst (pairFst q)) k
    (Nat.fromBitsLE (pairSnd q) + 1) (by omega)
  simpa only [BoundedCriticalSampleTestMoments.unitAccess, BoundedCriticalSampleTestMoments.unit,
    IntegerTarskiSeedBits.integerResidue, oneQuery, source, innerWord, modulusWord, pairFst_pair,
    pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode, Nat.add_sub_cancel] using H

noncomputable def coefficient (P : Readers) (f : List Bool → ℕ) (b : Bool) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (index z) = f (source z) then
    if Nat.fromBitsLE (outerWord z) = (if b then 1 else 0) then
      PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X])) (oneQuery z) else []
  else if Nat.fromBitsLE (outerWord z) = 0 then baseCode P b (baseQuery z) else []

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f) (b : Bool)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P f b) := by
  have hi := (BinaryFn.fromBits index_FP).eq (hf.comp source_FP)
  have hj := (BinaryFn.fromBits outerWord_FP).eq (BinaryFn.const (if b then 1 else 0))
  have h0 := (BinaryFn.fromBits outerWord_FP).eq (BinaryFn.const 0)
  have Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have U := DyadicConstantBits.oneCoefficientEvaluator.precompose oneQuery oneQuery_FP
  have E := (baseCode_evaluator h b ha).precompose baseQuery baseQuery_FP
  exact (SpaceFunction.branch _ hi.flag_mem_FP (SpaceFunction.branch _ hj.flag_mem_FP U Z)
    (SpaceFunction.branch _ h0.flag_mem_FP E Z)).congr
      (funext fun z => by simp only [coefficient, Function.comp_apply, decide_eq_true_eq])

theorem coefficient_packet (P : Readers) (f : List Bool → ℕ) (b : Bool) (q : List Bool) (k j : ℕ) :
    coefficient P f b (pair q (pair (BinaryNatCode.encode k) (BinaryNatCode.encode j))) =
      residueBits (((((family P f b).polynomial (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q)))).coeff j).coeff k : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  have hm : 0 < Nat.fromBitsLE (pairSnd q) + 1 := by omega
  simp only [coefficient, source, index, outerWord, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, family, polynomial]
  by_cases hi : Nat.fromBitsLE (pairSnd (pairFst q)) = f (pairFst (pairFst q))
  · rw [ite_eq_left hi, ite_eq_left hi]
    rw [free_coefficient]
    by_cases hj : j = (if b then 1 else 0)
    · rw [ite_eq_left hj, ite_eq_left hj]
      exact one_packet q k j
    · simp only [hj, ite_false, coeff_zero, Int.cast_zero, residueBits, ZMod.val_zero]
      rfl
  · rw [ite_eq_right hi, ite_eq_right hi, coeff_C]
    by_cases hj : j = 0
    · rw [ite_eq_left hj, ite_eq_left hj]
      have H := baseCode_packet P b (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd (pairFst q))) k (Nat.fromBitsLE (pairSnd q) + 1) hm
      simpa only [baseQuery, source, index, innerWord, modulusWord, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, BinaryNat.normalize_eq_bits, Nat.add_sub_cancel] using H
    · simp only [hj, ite_false, coeff_zero, Int.cast_zero, residueBits, ZMod.val_zero]
      rfl

noncomputable def access {P : Readers} (h : P.PolyTime) {f : List Bool → ℕ} (hf : BinaryFn f) (b : Bool)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : BivariateQueryProductBits.Access (family P f b) where
  reader := {
    coefficient := coefficient P f b
    evaluator := coefficient_evaluator h hf b ha
    coefficient_eq := coefficient_packet P f b }
  exponent _ := BinaryNatCode.encode 1
  exponent_eq _ _ := rfl
  exponent_FP := constFn_mem_FP _
  count_binary := BinaryFn.ofUnary ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 4))
  degree_binary := BinaryFn.const 1
  parameterDegree_binary := (BoundedCriticalRationalCoordinates.coordinateDegree_binary h).comp pairFst_mem_FP
  mass_binary := (BoundedCriticalRationalCoordinates.coordinateMass_binary h).comp pairFst_mem_FP

end LeanCanny.Encoding.BoundedCriticalSampleLineCoordinates

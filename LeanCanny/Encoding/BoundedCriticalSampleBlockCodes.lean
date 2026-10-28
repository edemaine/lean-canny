/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleBlockReaders

/-! # Sample-coordinate block codes with an independent exponent width

The width is a native control, independent of source term syntax. Free
coordinates become Kronecker monomials; frozen coordinates use the original
sample's rational-coordinate routines, including their zero extension.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleBlockCodes
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleBlockSource
open BoundedCriticalSampleBlockReaders (indexWord degreeWord indexWord_FP degreeWord_FP unitQuery unitQuery_FP free_pred)
open RationalSubstitution.IntegerBits (context selectedDegree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def span (W k : List Bool → ℕ) (u : List Bool) : ℕ := W u * (k u + 1)
def power (W o k : List Bool → ℕ) (u : List Bool) (i : ℕ) : ℕ :=
  2 ^ ((min (i - o u) (k u) + 1) * W u)

noncomputable def encoded (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if InBlock (o u) (k u) i then if b then X ^ power W o k u i else 1
  else BoundedCriticalSampleLineCoordinates.base P b u i

theorem encode_coordinate (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    FixedWidthKronecker.encode (k u + 1) (W u) (coordinate P o k b u i) = encoded P W o k b u i := by
  by_cases hi : InBlock (o u) (k u) i
  · have hm : min (i - o u) (k u) = i - o u := Nat.min_eq_left (by unfold InBlock at hi; omega)
    cases b
    · simp only [coordinate, encoded, hi, dite_true, ite_true, Bool.false_eq_true, ite_false, map_one]
    · simp only [coordinate, encoded, hi, dite_true, ite_true, FixedWidthKronecker.encode,
        MvPolynomial.eval₂Hom_X', freeVariable, power, hm]
  · simp only [coordinate, encoded, hi, dite_false, ite_false, IndexedMultivariateRational.encode_parameter]

theorem encoded_mass (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ) :
    coefficientMass (encoded P W o k b u i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := by
  unfold encoded
  split_ifs
  · rw [coefficientMass_X_pow]
    exact Nat.one_le_two_pow
  · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
      (Nat.one_le_two_pow : 1 ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u))
  · exact BoundedCriticalSampleLineCoordinates.base_mass P b u i

theorem encoded_degree (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i : ℕ)
    (hW : BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u) < 2 ^ W u) :
    (encoded P W o k b u i).natDegree ≤ 2 ^ span W k u := by
  unfold encoded
  split_ifs
  · rw [natDegree_X_pow]
    apply Nat.pow_le_pow_right (by decide)
    unfold span
    nlinarith [Nat.min_le_right (i - o u) (k u)]
  · simp only [natDegree_one, Nat.zero_le]
  · apply (BoundedCriticalSampleLineCoordinates.base_degree P b u i).trans
    apply hW.le.trans
    apply Nat.pow_le_pow_right (by decide)
    unfold span
    nlinarith

theorem power_binary {W o k : List Bool → ℕ} (hW : UnaryFn W) (ho : BinaryFn o) (hk : UnaryFn k) :
    BinaryFn (fun q => power W o k (context q) (Nat.fromBitsLE (indexWord q))) := by
  have hi := (BinaryFn.fromBits indexWord_FP).sub (ho.comp RationalSubstitution.IntegerBits.context_mem_FP)
  have hm : UnaryFn (fun q => min (Nat.fromBitsLE (indexWord q) - o (context q)) (k (context q))) :=
    (UnaryFn.fromBitsLE_min hi.bits_mem_FP (hk.comp RationalSubstitution.IntegerBits.context_mem_FP)).of_eq
      (fun q => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Function.comp_apply])
  exact (BinaryFn.const 2).powUnary ((hm.add (UnaryFn.const 1)).mul
    (hW.comp RationalSubstitution.IntegerBits.context_mem_FP))

noncomputable def coefficient (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (q : List Bool) : List Bool :=
  if InBlock (o (context q)) (k (context q)) (Nat.fromBitsLE (indexWord q)) then
    if b then if Nat.fromBitsLE (degreeWord q) = power W o k (context q) (Nat.fromBitsLE (indexWord q)) then
      IndexedKroneckerReader.unitValue (unitQuery q) else []
    else IndexedKroneckerReader.unitValue q
  else BoundedCriticalSampleLineCoordinates.baseCode P b q

theorem evaluator {P : Readers} (h : P.PolyTime) {W o k : List Bool → ℕ}
    (hW : UnaryFn W) (ho : BinaryFn o) (hk : UnaryFn k) (b : Bool)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P W o k b) := by
  have hi := (BinaryFn.fromBits degreeWord_FP).eq (power_binary hW ho hk)
  have U := SpaceFunction.ofFP _ IndexedKroneckerReader.unitValue_FP
  have E := SpaceFunction.branch _ hi.flag_mem_FP (U.precompose unitQuery unitQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have F : SpaceFunction (fun q => if b then
      (if Nat.fromBitsLE (degreeWord q) = power W o k (context q) (Nat.fromBitsLE (indexWord q)) then
        IndexedKroneckerReader.unitValue (unitQuery q) else []) else IndexedKroneckerReader.unitValue q) := by
    cases b
    · exact U
    · exact E.congr (funext fun q => by simp only [decide_eq_true_eq, Function.comp_apply, ite_true])
  exact (SpaceFunction.branch _ (free_pred ho hk).flag_mem_FP F
    (BoundedCriticalSampleLineCoordinates.baseCode_evaluator h b ha)).congr
      (funext fun q => by simp only [coefficient, decide_eq_true_eq])

theorem packet (P : Readers) (W o k : List Bool → ℕ) (b : Bool) (u : List Bool) (i j m : ℕ) (hm : 0 < m) :
    coefficient P W o k b
      (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) (BinaryNatCode.encode (m - 1))) =
        MatrixPower.residueBits (((encoded P W o k b u i).coeff j : ℤ) : ZMod m) := by
  simp only [coefficient, context, indexWord, degreeWord, selectedDegree, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, encoded]
  by_cases hi : InBlock (o u) (k u) i
  · rw [ite_eq_left hi, ite_eq_left hi]
    cases b
    · exact IndexedKroneckerReader.unit_packet u i j m hm
    · simp only [ite_true]
      by_cases hj : j = power W o k u i
      · rw [ite_eq_left hj, coeff_X_pow]
        simp only [← hj, ite_true]
        have H := IndexedKroneckerReader.unit_packet u i 0 m hm
        rw [show BinaryNatCode.encode 0 = [] from rfl] at H
        simpa only [unitQuery, context, selectedDegree, indexWord, pairFst_pair, pairSnd_pair,
          BinaryNatCode.encode, Polynomial.coeff_one_zero] using H
      · rw [ite_eq_right hj, coeff_X_pow]
        simp only [hj, ite_false, Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
        rfl
  · rw [ite_eq_right hi, ite_eq_right hi]
    exact BoundedCriticalSampleLineCoordinates.baseCode_packet P b u i j m hm

noncomputable def readers {P : Readers} (h : P.PolyTime) {W o k : List Bool → ℕ}
    (hW : UnaryFn W) (ho : BinaryFn o) (hk : UnaryFn k) (arity : List Bool → ℕ)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    RationalSubstitution.IntegerBits.CoordinateReaders arity (encoded P W o k true) (encoded P W o k false) where
  numerator := coefficient P W o k true
  denominator := coefficient P W o k false
  numeratorEvaluator := evaluator h hW ho hk true ha
  denominatorEvaluator := evaluator h hW ho hk false ha
  numerator_eq u i _ j m hm := packet P W o k true u i j m hm
  denominator_eq u i _ j m hm := packet P W o k false u i j m hm

end LeanCanny.Encoding.BoundedCriticalSampleBlockCodes

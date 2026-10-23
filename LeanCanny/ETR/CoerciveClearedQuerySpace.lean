/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveCoordinateEncoding
public import LeanCanny.ETR.CoerciveQueryIndexed
public import LeanCanny.Algebra.IndexedSource

/-! # Streamed multivariate clearing for the actual coercive sign queries -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveClearedQuerySpace
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open CoerciveSourceSampling CoercivePreparationControls CoerciveSymbolicSampling CoerciveInfinitesimalFamily
open CoerciveCoordinateEncoding (radix)
open Polynomial
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix
set_option allowUnsafeReducibility true in
attribute [local reducible] CoercivePreparationControls.family
attribute [local irreducible] CoerciveSourceSampling.dimension CoercivePowerReaders.size CoercivePowerReaders.width
attribute [local irreducible] CoercivePreparationControls.referenceExponent CoerciveSymbolicBounds.queryDegree
attribute [local irreducible] SymbolicFixedTableFinite.Family.fixedCoordinate SymbolicFixedTableFinite.Family.parameter
attribute [local irreducible] PolynomialKronecker.encode CoerciveSymbolicSampling.integerQuery CoerciveInfinitesimalFamily.queryIndex

noncomputable def numerator (c : List Bool) (i : ℕ) : ℤ[X] :=
  if hi : i < dimension (pairFst c) + 1 then
    PolynomialKronecker.encode (radix (pairFst c)) ((family (pairFst c)).fixedCoordinate ⟨i, hi⟩).numerator else 0
noncomputable def denominator (c : List Bool) (i : ℕ) : ℤ[X] :=
  if hi : i < dimension (pairFst c) + 1 then
    PolynomialKronecker.encode (radix (pairFst c)) ((family (pairFst c)).fixedCoordinate ⟨i, hi⟩).denominator else 0

noncomputable def indexedSource : RationalSubstitution.IntegerBits.IndexedSource :=
  RationalSubstitution.IntegerBits.IndexedSource.dense (fun c => dimension (pairFst c) + 1)
    (CoerciveQueryIndexed.width ∘ pairFst) (fun c => 2 * allowance (pairFst c))
    (fun c => CoerciveQueryIndexed.coefficient (pairFst c) (Nat.fromBitsLE (pairSnd c)))
    (fun c r i => CoerciveQueryIndexed.entry_le (pairFst c) r i)

noncomputable def substitution : RationalSubstitution.IntegerBits.Family :=
  indexedSource.withCoordinates numerator denominator

set_option backward.isDefEq.respectTransparency false in
theorem substitution_polynomial (c : List Bool) : substitution.polynomial c =
    PolynomialKronecker.encode (radix (pairFst c))
      (clearedQuery (pairFst c) (queryIndex (pairFst c) (Nat.fromBitsLE (pairSnd c)))) := by
  dsimp only [RationalSubstitution.IntegerBits.Family.polynomial, substitution, indexedSource,
    RationalSubstitution.IntegerBits.IndexedSource.withCoordinates, RationalSubstitution.IntegerBits.IndexedSource.dense, Function.comp_apply]
  rw [RationalSubstitution.Indexed.cleared_eq_clearedWith_source, CoerciveQueryIndexed.source_eq]
  have hn : (fun i : Fin (dimension (pairFst c) + 1) => numerator c i.val) =
      (fun i => PolynomialKronecker.encode (radix (pairFst c)) ((family (pairFst c)).fixedCoordinate i).numerator) := by
    funext i
    exact dite_eq_left i.isLt
  have hd : (fun i : Fin (dimension (pairFst c) + 1) => denominator c i.val) =
      (fun i => PolynomialKronecker.encode (radix (pairFst c)) ((family (pairFst c)).fixedCoordinate i).denominator) := by
    funext i
    exact dite_eq_left i.isLt
  rw [hn, hd]
  have he := BivariateRationalSubstitution.encode_clearedWith (radix (pairFst c))
    (fun _ : Fin (dimension (pairFst c) + 1) => allowance (pairFst c))
    (integerQuery (pairFst c) (queryIndex (pairFst c) (Nat.fromBitsLE (pairSnd c))))
    (fun i => ((family (pairFst c)).fixedCoordinate i).numerator)
    (fun i => ((family (pairFst c)).fixedCoordinate i).denominator)
  simpa only [clearedQuery, SymbolicFixedTableFinite.Family.signQueryWith, query, family] using he.symm

namespace Packet
open RationalSubstitution.IntegerBits

def input (p : List Bool) := pairFst (context p)
def row (p : List Bool) := pairSnd (context p)
def index (p : List Bool) := pairFst (selectedDegree p)
def degree (p : List Bool) := pairSnd (selectedDegree p)

theorem input_FP : input ∈ FP := mem_FP_comp context_mem_FP pairFst_mem_FP
theorem row_FP : row ∈ FP := mem_FP_comp context_mem_FP pairSnd_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp selectedDegree_mem_FP pairFst_mem_FP
theorem degree_FP : degree ∈ FP := mem_FP_comp selectedDegree_mem_FP pairSnd_mem_FP
end Packet

noncomputable def sourceProgram : List Bool → List Bool := CoerciveQueryIndexed.value Packet.input Packet.row
  RationalSubstitution.IntegerBits.selectedDegree pairSnd

theorem numerator_packet (R : CoerciveCoordinateEncoding.Readers) (c : List Bool)
    (i : Fin (dimension (pairFst c) + 1)) (k m : ℕ) (hm : 0 < m) :
    CoerciveCoordinateEncoding.numerator R Packet.input Packet.index Packet.degree pairSnd
      (pair (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((PolynomialKronecker.encode (radix (pairFst c))
        ((family (pairFst c)).fixedCoordinate i).numerator).coeff k : ℤ) : ZMod m) := by
  simp only [CoerciveCoordinateEncoding.numerator, Function.comp_apply, CoerciveCoordinateEncoding.request,
    Packet.input, Packet.index, Packet.degree, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNat.div_pair, BinaryNat.mod_pair,
    CoerciveCoordinateEncoding.radixCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have h := R.numerator_eq (pairFst c) i (k / radix (pairFst c)) (k % radix (pairFst c)) m hm
  have hB : (family (pairFst c)).exponent < radix (pairFst c) := by
    simpa only [CoercivePreparationControls.referenceExponent, CoerciveCoordinateEncoding.radix] using
      lt_of_le_of_lt (CoerciveCoordinateEncoding.reference_le_queryDegree (pairFst c))
        (Nat.lt_succ_self (CoerciveSymbolicBounds.queryDegree (pairFst c)))
  simp only [BinaryNatCode.encode] at h
  rw [h, (family (pairFst c)).coordinate_numerator_encoded (radix (pairFst c)) hB i k]
  rfl

theorem denominator_packet (R : CoerciveCoordinateEncoding.Readers) (c : List Bool)
    (i : Fin (dimension (pairFst c) + 1)) (k m : ℕ) (hm : 0 < m) :
    CoerciveCoordinateEncoding.denominator R Packet.input Packet.index Packet.degree pairSnd
      (pair (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (((PolynomialKronecker.encode (radix (pairFst c))
        ((family (pairFst c)).fixedCoordinate i).denominator).coeff k : ℤ) : ZMod m) := by
  simp only [CoerciveCoordinateEncoding.denominator, Function.comp_apply, CoerciveCoordinateEncoding.request,
    Packet.input, Packet.index, Packet.degree, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
    BinaryNat.normalize_eq_bits, BinaryNat.div_pair, BinaryNat.mod_pair,
    CoerciveCoordinateEncoding.radixCode, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have h := R.denominator_eq (pairFst c) i (k / radix (pairFst c)) (k % radix (pairFst c)) m hm
  have hB : (family (pairFst c)).exponent < radix (pairFst c) := by
    simpa only [CoercivePreparationControls.referenceExponent, CoerciveCoordinateEncoding.radix] using
      lt_of_le_of_lt (CoerciveCoordinateEncoding.reference_le_queryDegree (pairFst c))
        (Nat.lt_succ_self (CoerciveSymbolicBounds.queryDegree (pairFst c)))
  simp only [BinaryNatCode.encode] at h
  rw [h, (family (pairFst c)).coordinate_denominator_encoded (radix (pairFst c)) hB i k]
  rfl

noncomputable def sourceAccess : RationalSubstitution.IntegerBits.IndexedSource.Access indexedSource :=
  RationalSubstitution.IntegerBits.IndexedSource.denseAccess _ _ _ _
    (fun c r i => CoerciveQueryIndexed.entry_le (pairFst c) r i)
    (fun c => BinaryNatCode.encode (dimension (pairFst c) + 1))
    (fun c => BinaryNatCode.encode (2 * allowance (pairFst c))) sourceProgram
    (fun _ => Nat.fromBitsLE_bits _) (fun _ => Nat.fromBitsLE_bits _)
    (by
      intro c r _ m hm
      let p := pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))
      have hinput : Packet.input p = pairFst c := by
        simp only [p, Packet.input, RationalSubstitution.IntegerBits.context, pairFst_pair]
      have hmod : Nat.fromBitsLE (pairSnd p) + 1 = m := by
        simp only [p, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
          Nat.sub_add_cancel (show 1 ≤ m by omega)]
      have h := CoerciveQueryIndexed.value_eq Packet.input Packet.row
        RationalSubstitution.IntegerBits.selectedDegree pairSnd p
      rw [hinput, hmod] at h
      simpa only [p, Packet.input, Packet.row, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (show 1 ≤ m by omega),
        CoerciveQueryIndexed.coefficient, sourceProgram, substitution] using h)

noncomputable def coordinateReaders (R : CoerciveCoordinateEncoding.Readers) :
    RationalSubstitution.IntegerBits.CoordinateReaders (fun c => dimension (pairFst c) + 1) numerator denominator where
  numerator := CoerciveCoordinateEncoding.numerator R Packet.input Packet.index Packet.degree pairSnd
  denominator := CoerciveCoordinateEncoding.denominator R Packet.input Packet.index Packet.degree pairSnd
  numeratorEvaluator := CoerciveCoordinateEncoding.numerator_evaluator R Packet.input_FP Packet.index_FP Packet.degree_FP pairSnd_mem_FP
  denominatorEvaluator := CoerciveCoordinateEncoding.denominator_evaluator R Packet.input_FP Packet.index_FP Packet.degree_FP pairSnd_mem_FP
  numerator_eq c i hi k m hm := by
    change i < dimension (pairFst c) + 1 at hi
    simpa only [numerator, dite_eq_left hi, family] using numerator_packet R c ⟨i, hi⟩ k m hm
  denominator_eq c i hi k m hm := by
    change i < dimension (pairFst c) + 1 at hi
    simpa only [denominator, dite_eq_left hi, family] using denominator_packet R c ⟨i, hi⟩ k m hm

noncomputable def access (R : CoerciveCoordinateEncoding.Readers) : RationalSubstitution.IntegerBits.Access substitution :=
  RationalSubstitution.IntegerBits.IndexedSource.access sourceAccess (coordinateReaders R)

theorem controls (R : CoerciveCoordinateEncoding.Readers) : (access R).ControlsPolyTime := by
  constructor
  · exact bits_mem_FP ((dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1))
  · exact bits_mem_FP ((UnaryFn.const 2).mul (CoerciveSymbolicBounds.allowance_unary.comp pairFst_mem_FP))
  · exact FixedWidthPolynomial.countCode_mem_FP
      ((dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)) (CoerciveQueryIndexed.width_unary.comp pairFst_mem_FP)
  · exact FixedWidthPolynomial.exponentRead_mem_FP
      ((dimension_unary.comp pairFst_mem_FP).add (UnaryFn.const 1)) (CoerciveQueryIndexed.width_unary.comp pairFst_mem_FP)

theorem encodedEvaluator (R : CoerciveCoordinateEncoding.Readers) : SpaceFunction substitution.value :=
  (access R).evaluator (controls R)
    (CoerciveQueryIndexed.evaluator Packet.input_FP Packet.row_FP RationalSubstitution.IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)
    (coordinateReaders R).numeratorEvaluator (coordinateReaders R).denominatorEvaluator

end LeanCanny.ETR.CoerciveClearedQuerySpace

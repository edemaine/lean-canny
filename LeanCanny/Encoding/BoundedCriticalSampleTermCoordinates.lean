/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleCoordinateTests
public import LeanCanny.Encoding.BoundedCriticalFilterCoefficients
public import LeanCanny.ETR.EncodedRationalSubstitution

/-! # Native sample coordinates for encoded arithmetic terms

The source context is `pair original queryIndex`. Coordinates retain the
original source and extend the actual sample tuple by zero beyond its
dimension. The corresponding rational coordinates are zero over one there,
so clearing denominators is valid for every encoded arithmetic term.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleTermCoordinates
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open RationalSubstitutionBits RationalSubstitution.IntegerBits MatrixPower Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate PrimitivePairBits.coefficient
  BoundedCriticalRationalCoordinates.coordinateDegree BoundedCriticalRationalCoordinates.coordinateMass

noncomputable def numerator (P : Readers) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if i < P.dim (pairFst u) + 4 then BoundedCriticalFilters.numerator P (pairFst u) i else 0
noncomputable def denominator (P : Readers) (u : List Bool) (i : ℕ) : ℤ[X] :=
  if i < P.dim (pairFst u) + 4 then BoundedCriticalFilters.denominator P (pairFst u) i else 1

def validIndex (P : Readers) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairFst (selectedDegree q)) < P.dim (pairFst (context q)) + 4

theorem validIndex_pred {P : Readers} (h : P.PolyTime) : FPPred (validIndex P) := by
  have hi := BinaryFn.fromBits (mem_FP_comp selectedDegree_mem_FP pairFst_mem_FP)
  have hn : BinaryFn (fun q => P.dim (pairFst (context q)) + 4) :=
    (BinaryFn.ofUnary (h.dim.comp (mem_FP_comp context_mem_FP pairFst_mem_FP))).add (BinaryFn.const 4)
  exact hi.lt hn

def unitQuery (q : List Bool) : List Bool :=
  pair (pair (context q) (pairSnd (selectedDegree q))) (pairSnd q)
theorem unitQuery_FP : unitQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair context_mem_FP (mem_FP_comp selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def numeratorCode (P : Readers) (q : List Bool) : List Bool :=
  if validIndex P q then BoundedCriticalFilterCoefficients.numerator P q else []
noncomputable def denominatorCode (P : Readers) (q : List Bool) : List Bool :=
  if validIndex P q then BoundedCriticalFilterCoefficients.denominator P q else
    PrimitivePairBits.coefficient (fun _ => (1 : ℤ[X])) (unitQuery q)

theorem numerator_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (numeratorCode P) := by
  have E := (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).1.precompose
    FiniteLeafSignBits.coordinateQuery FiniteLeafSignBits.coordinateQuery_FP
  exact (SpaceFunction.branch _ (validIndex_pred h).flag_mem_FP E (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
    (funext fun q => by simp only [numeratorCode, Function.comp_apply, decide_eq_true_eq]; rfl)

theorem denominator_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (denominatorCode P) := by
  have E := (BoundedCriticalRationalCoordinates.coefficient_evaluators h ha).2.precompose
    FiniteLeafSignBits.coordinateQuery FiniteLeafSignBits.coordinateQuery_FP
  have U := DyadicConstantBits.oneCoefficientEvaluator.precompose unitQuery unitQuery_FP
  exact (SpaceFunction.branch _ (validIndex_pred h).flag_mem_FP E U).congr
    (funext fun q => by simp only [denominatorCode, Function.comp_apply, decide_eq_true_eq]; rfl)

theorem numerator_packet (P : Readers) (u : List Bool) (i k m : ℕ) (hm : 0 < m) :
    numeratorCode P (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((numerator P u i).coeff k : ℤ) : ZMod m) := by
  have hv : validIndex P (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) ↔
      i < P.dim (pairFst u) + 4 := by
    simp only [validIndex, context, selectedDegree, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases hi : i < P.dim (pairFst u) + 4
  · rw [numeratorCode, ite_eq_left (hv.mpr hi), numerator, ite_eq_left hi]
    exact (BoundedCriticalFilterCoefficients.access P).numerator_eq u i hi k m hm
  · rw [numeratorCode, ite_eq_right (fun h => hi (hv.mp h)), numerator, ite_eq_right hi]
    simp only [coeff_zero, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

theorem denominator_packet (P : Readers) (u : List Bool) (i k m : ℕ) (hm : 0 < m) :
    denominatorCode P (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((denominator P u i).coeff k : ℤ) : ZMod m) := by
  have hv : validIndex P (pair (pair u (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) ↔
      i < P.dim (pairFst u) + 4 := by
    simp only [validIndex, context, selectedDegree, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  by_cases hi : i < P.dim (pairFst u) + 4
  · rw [denominatorCode, ite_eq_left (hv.mpr hi), denominator, ite_eq_left hi]
    exact (BoundedCriticalFilterCoefficients.access P).denominator_eq u i hi k m hm
  · rw [denominatorCode, ite_eq_right (fun h => hi (hv.mp h)), denominator, ite_eq_right hi]
    simp only [PrimitivePairBits.coefficient, unitQuery, coefficientResidue, context, selectedDegree,
      mValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      rfl (by rw [pairSnd_pair, Nat.fromBitsLE_bits]; omega)

noncomputable def coordinates (P : Readers) (S : Source) : Coordinates S where
  numerator := numerator P
  denominator := denominator P
  numeratorCode := numeratorCode P
  denominatorCode := denominatorCode P
  numerator_eq u i _ k m hm := numerator_packet P u i k m hm
  denominator_eq u i _ k m hm := denominator_packet P u i k m hm

theorem numerator_degree (P : Readers) (u : List Bool) (i : ℕ) :
    (numerator P u i).natDegree ≤ BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u) := by
  unfold numerator
  split_ifs
  · simpa only [BoundedCriticalFilters.numerator, pairFst_pair] using
      (Nat.le_max_left _ _).trans (BoundedCriticalRationalCoordinates.coordinate_bounds P (pair (pairFst u) (BinaryNatCode.encode i))).1
  · simp only [natDegree_zero, Nat.zero_le]

theorem denominator_degree (P : Readers) (u : List Bool) (i : ℕ) :
    (denominator P u i).natDegree ≤ BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst u) := by
  unfold denominator
  split_ifs
  · simpa only [BoundedCriticalFilters.denominator, pairFst_pair] using
      (Nat.le_max_right _ _).trans (BoundedCriticalRationalCoordinates.coordinate_bounds P (pair (pairFst u) (BinaryNatCode.encode i))).1
  · simp only [natDegree_one, Nat.zero_le]

theorem numerator_mass (P : Readers) (u : List Bool) (i : ℕ) :
    coefficientMass (numerator P u i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := by
  unfold numerator
  split_ifs
  · simpa only [BoundedCriticalFilters.numerator, pairFst_pair] using
      (BoundedCriticalRationalCoordinates.coordinate_bounds P (pair (pairFst u) (BinaryNatCode.encode i))).2.1
  · simp only [coefficientMass_zero, Nat.zero_le]

theorem denominator_mass (P : Readers) (u : List Bool) (i : ℕ) :
    coefficientMass (denominator P u i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u) := by
  unfold denominator
  split_ifs
  · simpa only [BoundedCriticalFilters.denominator, pairFst_pair] using
      (BoundedCriticalRationalCoordinates.coordinate_bounds P (pair (pairFst u) (BinaryNatCode.encode i))).2.2
  · simpa only [← Polynomial.C_1, coefficientMass_C, Int.natAbs_one] using
      (Nat.one_le_two_pow : 1 ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P (pairFst u))

theorem denominator_nonzero (P : Readers) (c d : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (i : ℕ) :
    (denominator P (pair c d) i).eval₂ (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val ≠ 0 := by
  simp only [denominator, pairFst_pair]
  split_ifs with hi
  · exact BoundedCriticalSampleCoordinateTests.denominator_nonzero P c x ⟨i, hi⟩
  · simp only [eval₂_one, ne_eq, one_ne_zero, not_false_eq_true]

theorem coordinate_eval (P : Readers) (c d : List Bool) (x : BoundedFullCriticalSamples.Samples P c) (i : ℕ) :
    (numerator P (pair c d) i).eval₂ (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val /
      (denominator P (pair c d) i).eval₂ (Int.castRingHom ℝ) (BoundedCriticalSampleLabels.parameter P c x).val =
        Formula.extend x.val i := by
  simp only [numerator, denominator, pairFst_pair, Formula.extend]
  split_ifs with hi
  · exact BoundedCriticalSampleCoordinateTests.coordinate_eval P c x ⟨i, hi⟩
  · simp only [eval₂_zero, eval₂_one, zero_div]

end LeanCanny.Encoding.BoundedCriticalSampleTermCoordinates

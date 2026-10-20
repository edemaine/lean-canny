/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterBounds
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Signs and zero tests for specialized regular-system spatial coefficients

Certified parameter-coordinate readers and binary bounds suffice. Both original
source coefficients and the complete substitution computation are charged as
suspended children. Effective parameter selection remains a separate task.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open Complexity LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Algebra.RationalSubstitution Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm IntegerBits.Family.polynomial

noncomputable def selectedCoefficient (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (q : List Bool) : ℤ := ((family source active row n d).polynomial (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))

noncomputable def selectedBudget (source degree bits : List Bool → List Bool) : List Bool → List Bool :=
  budgetCode source degree bits ∘ pairFst

theorem selectedBudget_mem_FP {source degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : degree ∈ FP) (hb : bits ∈ FP) : selectedBudget source degree bits ∈ FP :=
  mem_FP_comp pairFst_mem_FP (budgetCode_mem_FP hs hE hb)

theorem selectedCoefficient_bits (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : CoordinateBounds source n d) (q : List Bool) :
    (selectedCoefficient source active row n d q).natAbs.size ≤ Nat.fromBitsLE (selectedBudget source B.degree B.bits q) := by
  dsimp only [selectedCoefficient, selectedBudget, Function.comp_apply]
  exact polynomial_coefficient_bits source active row n d B (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem selectedCoefficient_packet (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (q : List Bool) (m : ℕ) (hm : 0 < m) :
    (family source active row n d).value (pair q (BinaryNatCode.encode (m - 1))) =
      residueBits ((selectedCoefficient source active row n d q : ℤ) : ZMod m) :=
  IntegerBits.Family.value_packet _ q m hm

noncomputable def signValue (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (q : List Bool) : List Bool :=
  if selectedCoefficient source active row n d q = 0 then []
  else if selectedCoefficient source active row n d q < 0 then [true] else [false, true]

noncomputable def signumEvaluator (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (B : CoordinateBounds source n d) (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (signValue source active row n d) :=
  IntegerSignumBits.evaluator (evaluator source active row n d C hs ha hr)
    (selectedBudget source B.degree B.bits) (selectedBudget_mem_FP hs B.degreeFP B.bitsFP)
    (selectedCoefficient source active row n d) (selectedCoefficient_bits source active row n d B)
    (selectedCoefficient_packet source active row n d)

theorem zeroLanguage_mem_PSPACE (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (B : CoordinateBounds source n d) (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {q | selectedCoefficient source active row n d q = 0} ∈ PSPACE :=
  IntegerZeroBits.zeroLanguage_mem_PSPACE (evaluator source active row n d C hs ha hr)
    (selectedBudget source B.degree B.bits) (selectedBudget_mem_FP hs B.degreeFP B.bitsFP)
    (selectedCoefficient source active row n d) (selectedCoefficient_bits source active row n d B)
    (selectedCoefficient_packet source active row n d)


noncomputable def trailingSignEvaluator (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (C : CoordinateReaders source n d) (B : CoordinateBounds source n d) (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (fun c => InfinitesimalSign.tag ((family source active row n d).polynomial c).trailingCoeff) :=
  (access source active row n d C).signEvaluator (access_controls source active row n d C hs)
    (coefficientEvaluator source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator
    B.degree B.bits (sourceBits source) B.degreeFP B.bitsFP (sourceBits_mem_FP hs)
    (fun c r _ => source_coefficient_bound source active row c r)
    B.numerator_degree B.denominator_degree B.numerator_coeff B.denominator_coeff

end LeanCanny.ETR.TubeParameter

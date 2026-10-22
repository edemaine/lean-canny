/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalBounds
public import LeanCanny.Algebra.RationalSubstitutionSign
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Coefficient decisions and infinitesimal signs after tube substitution

Actual tube/projection residue readers, certified rational-coordinate readers,
and coordinate bounds yield full coefficient sign/zero routines and the sign
at a sufficiently small positive parameter. No source coefficient callback or
output-degree oracle is required.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational

open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open Algebra.MatrixPower Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm IntegerBits.Family.polynomial

noncomputable def selectedCoefficient (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (q : List Bool) : ℤ :=
  ((family projection source active row n d).polynomial (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q))

noncomputable def selectedBudget (projection : Bool) (source degree bits : List Bool → List Bool) : List Bool → List Bool :=
  budgetCode projection source degree bits ∘ pairFst

theorem selectedBudget_mem_FP (projection : Bool) {source degree bits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : degree ∈ FP) (hb : bits ∈ FP) : selectedBudget projection source degree bits ∈ FP :=
  mem_FP_comp pairFst_mem_FP (budgetCode_mem_FP projection hs hE hb)

theorem selectedCoefficient_bits (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (B : CoordinateBounds projection source n d) (q : List Bool) :
    (selectedCoefficient projection source active row n d q).natAbs.size ≤ Nat.fromBitsLE (selectedBudget projection source B.degree B.bits q) := by
  dsimp only [selectedCoefficient, selectedBudget, Function.comp_apply]
  exact polynomial_coefficient_bits projection source active row n d B (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem selectedCoefficient_packet (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (q : List Bool) (m : ℕ) (hm : 0 < m) :
    (family projection source active row n d).value (pair q (BinaryNatCode.encode (m - 1))) =
      residueBits ((selectedCoefficient projection source active row n d q : ℤ) : ZMod m) :=
  IntegerBits.Family.value_packet _ q m hm

theorem coefficientNegativeEvaluator (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (fun q => if selectedCoefficient projection source active row n d q < 0 then [true] else []) :=
  Algebra.IntegerSignBits.evaluator (evaluator projection source active row n d C hs ha hr)
    (selectedBudget projection source B.degree B.bits) (selectedBudget_mem_FP projection hs B.degreeFP B.bitsFP)
    (selectedCoefficient projection source active row n d) (selectedCoefficient_bits projection source active row n d B)
    (selectedCoefficient_packet projection source active row n d)

theorem coefficientNegativeLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {q | selectedCoefficient projection source active row n d q < 0} ∈ PSPACE :=
  Algebra.IntegerSignBits.negativeLanguage_mem_PSPACE (evaluator projection source active row n d C hs ha hr)
    (selectedBudget projection source B.degree B.bits) (selectedBudget_mem_FP projection hs B.degreeFP B.bitsFP)
    (selectedCoefficient projection source active row n d) (selectedCoefficient_bits projection source active row n d B)
    (selectedCoefficient_packet projection source active row n d)

theorem coefficientZeroDecider (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceDecider {q | selectedCoefficient projection source active row n d q = 0} :=
  Algebra.IntegerZeroBits.zeroDecider (evaluator projection source active row n d C hs ha hr)
    (selectedBudget projection source B.degree B.bits) (selectedBudget_mem_FP projection hs B.degreeFP B.bitsFP)
    (selectedCoefficient projection source active row n d) (selectedCoefficient_bits projection source active row n d B)
    (selectedCoefficient_packet projection source active row n d)

theorem coefficientZeroLanguage_mem_PSPACE (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    {q | selectedCoefficient projection source active row n d q = 0} ∈ PSPACE :=
  (coefficientZeroDecider projection source active row n d C B hs ha hr).mem_PSPACE

theorem signEvaluator (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (C : CoordinateReaders projection source n d) (B : CoordinateBounds projection source n d)
    (hs : source ∈ FP) (ha : active ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (fun c => Algebra.InfinitesimalSign.tag ((family projection source active row n d).polynomial c).trailingCoeff) :=
  (access projection source active row n d C).signEvaluator (access_controls projection source active row n d C hs)
    (coefficientEvaluator projection source active row hs ha hr) C.numeratorEvaluator C.denominatorEvaluator
    B.degree B.bits (sourceBits source) B.degreeFP B.bitsFP (sourceBits_mem_FP hs)
    (fun c r _ => source_coefficient_bound projection source active row c r)
    B.numerator_degree B.denominator_degree B.numerator_coeff B.denominator_coeff

end LeanCanny.ETR.TubeRational

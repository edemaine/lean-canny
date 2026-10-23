/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSourceCoefficient
public import LeanCanny.ETR.TubeSourceProjectionCoefficient
public import LeanCanny.ETR.TubeCoefficientBounds
public import LeanCanny.Algebra.IntegerSignSpace
public import LeanCanny.Algebra.IntegerZeroSpace
public import LeanCanny.Algebra.IntegerSignumSpace

/-! # Full tube and projection coefficient signs and zero tests

The actual coefficient mass bounds supply the FP magnitude-bit budgets.
Lifted query fields let the complete residue machines answer the CRT and zero
scan packets without rebuilding or guessing polynomial coefficients.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSourceCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerPolynomial TubeCoefficient.value

def budget : List Bool → List Bool := TubeSource.coefficientBits ∘ input

theorem budget_mem_FP : budget ∈ FP := mem_FP_comp input_mem_FP TubeSource.coefficientBits_FP

theorem coefficient_bits (q : List Bool) : (coefficient q).natAbs.size ≤ Nat.fromBitsLE (budget q) := by
  change ((TubeSource.integerPolynomial (input q) (activeSet (CompactSource.term (input q)).arity (active q))).coeff
    (TubeZeroQuery.exponent (TubeDense.arity base) width target q)).natAbs.size ≤ Nat.fromBitsLE (TubeSource.coefficientBits (input q))
  exact TubeSource.integer_polynomial_coefficient_bits _ _ _

noncomputable def residue : List Bool → List Bool :=
  TubeCoefficient.value (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (target ∘ pairFst) pairSnd

theorem residueEvaluator : SpaceFunction residue :=
  TubeCoefficient.evaluator (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (target ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP base_mem_FP) (width_unary.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP active_mem_FP) (mem_FP_comp pairFst_mem_FP target_mem_FP) pairSnd_mem_FP

theorem coefficient_lift (q : List Bool) :
    TubeCoefficient.coefficient (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (target ∘ pairFst) q = coefficient (pairFst q) := rfl

theorem residue_packet (c : List Bool) (m : ℕ) (hm : 0 < m) :
    residue (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((coefficient c : ℤ) : ZMod m) := by
  unfold residue TubeCoefficient.value
  rw [coefficient_lift, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

theorem negativeEvaluator : SpaceFunction (fun c => if coefficient c < 0 then [true] else []) :=
  Algebra.IntegerSignBits.evaluator residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem negativeLanguage_mem_PSPACE : {c | coefficient c < 0} ∈ PSPACE :=
  Algebra.IntegerSignBits.negativeLanguage_mem_PSPACE residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem zeroDecider : SpaceDecider {c | coefficient c = 0} :=
  Algebra.IntegerZeroBits.zeroDecider residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem zeroLanguage_mem_PSPACE : {c | coefficient c = 0} ∈ PSPACE := zeroDecider.mem_PSPACE

theorem signumEvaluator :
    SpaceFunction (fun c => if coefficient c = 0 then [] else if coefficient c < 0 then [true] else [false, true]) :=
  Algebra.IntegerSignumBits.evaluator residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem positiveLanguage_mem_PSPACE : {c | 0 < coefficient c} ∈ PSPACE :=
  Algebra.IntegerSignumBits.positiveLanguage_of_signum coefficient signumEvaluator

end LeanCanny.ETR.TubeSourceCoefficient

namespace LeanCanny.ETR.TubeSourceProjectionCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerProjection TubeProjection.value

def budget : List Bool → List Bool := TubeSource.coefficientBits ∘ input

theorem budget_mem_FP : budget ∈ FP := mem_FP_comp input_mem_FP TubeSource.coefficientBits_FP

theorem coefficient_bits (q : List Bool) : (coefficient q).natAbs.size ≤ Nat.fromBitsLE (budget q) := by
  change ((TubeSource.integerProjection (input q) (activeSet (CompactSource.term (input q)).arity (active q))
    (TubeProjection.decodedRow base row q)).coeff (TubeProjectionQuery.exponent (TubeDense.arity base) width target q)).natAbs.size ≤
      Nat.fromBitsLE (TubeSource.coefficientBits (input q))
  exact TubeSource.integer_projection_coefficient_bits _ _ _ _

noncomputable def residue : List Bool → List Bool :=
  TubeProjection.value (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) (target ∘ pairFst) pairSnd

theorem residueEvaluator : SpaceFunction residue :=
  TubeProjection.evaluator (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) (target ∘ pairFst) pairSnd
    (mem_FP_comp pairFst_mem_FP base_mem_FP) (width_unary.comp pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP active_mem_FP) (mem_FP_comp pairFst_mem_FP row_mem_FP)
    (mem_FP_comp pairFst_mem_FP target_mem_FP) pairSnd_mem_FP

theorem coefficient_lift (q : List Bool) :
    TubeProjection.coefficient (base ∘ pairFst) (width ∘ pairFst) (active ∘ pairFst) (row ∘ pairFst) (target ∘ pairFst) q = coefficient (pairFst q) := rfl

theorem residue_packet (c : List Bool) (m : ℕ) (hm : 0 < m) :
    residue (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((coefficient c : ℤ) : ZMod m) := by
  unfold residue
  rw [TubeProjection.value_eq_coefficient, coefficient_lift, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]

theorem negativeEvaluator : SpaceFunction (fun c => if coefficient c < 0 then [true] else []) :=
  Algebra.IntegerSignBits.evaluator residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem negativeLanguage_mem_PSPACE : {c | coefficient c < 0} ∈ PSPACE :=
  Algebra.IntegerSignBits.negativeLanguage_mem_PSPACE residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem zeroDecider : SpaceDecider {c | coefficient c = 0} :=
  Algebra.IntegerZeroBits.zeroDecider residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem zeroLanguage_mem_PSPACE : {c | coefficient c = 0} ∈ PSPACE := zeroDecider.mem_PSPACE

theorem signumEvaluator :
    SpaceFunction (fun c => if coefficient c = 0 then [] else if coefficient c < 0 then [true] else [false, true]) :=
  Algebra.IntegerSignumBits.evaluator residueEvaluator budget budget_mem_FP coefficient coefficient_bits residue_packet

theorem positiveLanguage_mem_PSPACE : {c | 0 < coefficient c} ∈ PSPACE :=
  Algebra.IntegerSignumBits.positiveLanguage_of_signum coefficient signumEvaluator

end LeanCanny.ETR.TubeSourceProjectionCoefficient

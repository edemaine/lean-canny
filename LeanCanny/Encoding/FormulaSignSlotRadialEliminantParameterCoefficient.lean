/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterReadback
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantPacked
/-! # Original-only streamed coefficients of the packed actual homogeneous rows

The only dense call is the frozen original squared-source derivative routine.
All remaining operations are sparse guards and modular arithmetic. Requests
outside the complete parameter box return the actual zero coefficient.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterCoefficient
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower MvPolynomial
open FormulaSignSlotRadialEliminantParameterQuery
open scoped Classical
set_option backward.isDefEq.respectTransparency false

local instance radialParameterCoefficientDimensionNeZero (q : List Bool) : NeZero (parameterDimension q) :=
  ⟨by unfold parameterDimension; omega⟩

noncomputable def coordinate (q : List Bool) : Fin (spatial q) := FormulaSignSlotRadialEliminantInput.coordinate (context q)
noncomputable def row (q : List Bool) : Fin (spatial q + 1) :=
  ⟨min (Nat.fromBitsLE (rowWord q)) (spatial q), Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
noncomputable def gradientRow (q : List Bool) : Fin (spatial q) :=
  ⟨(row q).val - 1, by
    have HM : 0 < spatial q := by
      unfold spatial FormulaSignSlotRadialEliminantPackingLayout.spatial FormulaSignSlotRadialFormalInput.spatial
      omega
    have HR := (row q).isLt
    omega⟩


theorem coordinate_unary : UnaryFn (fun q => (coordinate q).val) :=
  FormulaSignSlotRadialEliminantInput.coordinate_unary.comp context_FP
theorem row_unary : UnaryFn (fun q => (row q).val) := UnaryFn.fromBitsLE_min rowWord_FP spatial_unary
theorem gradientRow_unary : UnaryFn (fun q => (gradientRow q).val) := row_unary.sub (UnaryFn.const 1)

noncomputable def rawProgram (q : List Bool) : List Bool :=
  if (row q).val = 0 then
    FormulaSignSlotRadialEliminantCoefficientNative.coordinateValue original sourceWidth sourceWord headWord
      epsilonWord targetWord modulus coordinate q
  else FormulaSignSlotRadialEliminantCoefficientNative.gradientValue original sourceWidth sourceWord headWord
    epsilonWord targetWord modulus gradientRow q

theorem rawProgram_evaluator : SpaceFunction rawProgram := by
  have EA := SpaceFunction.ofFP _ (FormulaSignSlotRadialEliminantCoefficientNative.coordinate_value_FP
    original original_FP sourceWidth sourceWidth_unary sourceWord headWord epsilonWord targetWord modulus
    sourceWord_FP headWord_FP epsilonWord_FP targetWord_FP modulus_FP coordinate coordinate_unary)
  have EB := FormulaSignSlotRadialEliminantCoefficientNative.gradient_evaluator
    original original_FP sourceWidth sourceWidth_unary sourceWord headWord epsilonWord targetWord modulus
    sourceWord_FP headWord_FP epsilonWord_FP targetWord_FP modulus_FP gradientRow gradientRow_unary
  have E := SpaceFunction.branch (fun q => decide ((row q).val = 0))
    (FPPred.eq row_unary (UnaryFn.const 0)).flag_mem_FP EA EB
  exact E.congr (funext fun q => by simp only [rawProgram, decide_eq_true_eq])

noncomputable def rawCoefficient (q : List Bool) : ℤ :=
  ((FormulaSignSlotRadialEliminantParameterRows.row (original q) (coordinate q) (row q)).coeff
    (spatialExponent q)).coeff (parameterExponent q)

private theorem exponent_roundtrip {a : ℕ} (f : Fin (a + 3) →₀ ℕ) :
    TriplePolynomialParameterFlatten.exponent (f 0) (f.tail 0) (f.tail.tail 0) f.tail.tail.tail = f := by
  simp only [TriplePolynomialParameterFlatten.exponent, Finsupp.cons_tail]

private theorem coefficient_reconstruction (q : List Bool) (r : Fin (spatial q + 1)) :
    (FormulaSignSlotRadialEliminantRows.polynomial (original q) (coordinate q) r).coeff
      (FormulaSignSlotRadialEliminantRows.exponent
        ((FormulaSignSlotRadialEliminantCoefficientNative.homogeneousExponent original sourceWidth sourceWord headWord q).mapDomain
          CoerciveCriticalHomogenization.layout)
        (Nat.fromBitsLE (epsilonWord q)) (Nat.fromBitsLE (targetWord q))
        (FormulaSignSlotRadialEliminantCoefficientQuery.radius (original q) (sourceExponent q))
        (FormulaSignSlotRadialEliminantCoefficientQuery.center (original q) (sourceExponent q))) =
      ((FormulaSignSlotRadialEliminantParameterRows.row (original q) (coordinate q) r).coeff
        (spatialExponent q)).coeff (parameterExponent q) := by
  have HE : TriplePolynomialParameterFlatten.exponent (parameterExponent q 0)
      ((parameterExponent q).tail 0) ((parameterExponent q).tail.tail 0)
      (parameterExponent q).tail.tail.tail = parameterExponent q := by
    exact exponent_roundtrip (a := centers q) (parameterExponent q)
  erw [homogeneous_readback, epsilon_readback, target_readback, radius_parameter, center_parameter,
    FormulaSignSlotRadialEliminantRows.coefficient,
    ← FormulaSignSlotRadialEliminantParameterRows.coefficient, HE]

theorem rawProgram_correct (q : List Bool) :
    rawProgram q = residueBits (rawCoefficient q : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  unfold rawProgram
  split_ifs with HR
  · have HE : row q = CoerciveCriticalHomogenization.layout none := by
      apply Fin.ext
      simpa only [CoerciveHomogeneousLayout.layout_none, Fin.val_zero] using HR
    erw [FormulaSignSlotRadialEliminantCoefficientNative.coordinateValue_correct,
      coefficient_reconstruction]
    rw [rawCoefficient, HE]
    rfl
  · have HE : row q = CoerciveCriticalHomogenization.layout (some (gradientRow q)) := by
      apply Fin.ext
      simp only [CoerciveHomogeneousLayout.layout_some, Fin.val_succ, gradientRow]
      have HP : 0 < (row q).val := by omega
      omega
    erw [FormulaSignSlotRadialEliminantCoefficientNative.gradientValue_correct
      original sourceWidth sourceWord headWord epsilonWord targetWord modulus gradientRow q (coordinate q),
      coefficient_reconstruction]
    rw [rawCoefficient, HE]
    rfl

noncomputable def value (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (parameterWord q) < FormulaSignSlotRadialEliminantPacked.parameterBox (context q)
  then rawProgram q else []

theorem evaluator : SpaceFunction value := by
  have HG := (BinaryFn.fromBits parameterWord_FP).lt
    (FormulaSignSlotRadialEliminantPacked.parameterBox_binary.comp context_FP)
  have E := SpaceFunction.branch
    (fun q => decide (Nat.fromBitsLE (parameterWord q) < FormulaSignSlotRadialEliminantPacked.parameterBox (context q)))
    HG.flag_mem_FP rawProgram_evaluator (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq])

theorem correct (q : List Bool) : value q =
    residueBits (((((FormulaSignSlotRadialEliminantPacked.system (context q) (row q)).coeff
      (spatialExponent q)).coeff (Nat.fromBitsLE (parameterWord q))) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  unfold value
  split_ifs with HFit
  · rw [rawProgram_correct]
    let k : Fin (FormulaSignSlotRadialEliminantPacked.parameterBox (context q)) := ⟨_, HFit⟩
    have H := FormulaSignSlotRadialEliminantPacked.coefficient (context q) (row q) (spatialExponent q) k
    have HE : FixedWidthPolynomial.vector (centers q + 3) (parameterWidth q) k = parameterExponent q := by
      rw [← FixedWidthPolynomial.entry_vector]
      rfl
    erw [HE] at H
    exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (modulus q) + 1))) H.symm
  · rw [FormulaSignSlotRadialEliminantPacked.coefficient_of_ge (context q) (row q) (spatialExponent q)
      _ (by omega), Int.cast_zero]
    rfl

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterCoefficient

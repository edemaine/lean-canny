/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueCoefficientNative
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueMass
/-! # Original-only source metadata and coefficients for actual value-certificate coefficients

Context is the value family context paired with order and radius degree.
The center variables remain formal integer variables throughout.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph

def order (z : List Bool) := Nat.fromBitsLE (pairFst (pairSnd z))
def radius (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
noncomputable def arity (z : List Bool) := d (FormulaSignSlotRadialCenterValueLayout.original (pairFst z))
noncomputable def width (z : List Bool) := FormulaSignSlotRadialCenterValuePacking.width (pairFst z)
noncomputable def degree (z : List Bool) := FormulaSignSlotRadialCenterValuePacking.degree (pairFst z)
noncomputable def mass (z : List Bool) := FormulaSignSlotRadialCenterValueMass.budget (pairFst z)
noncomputable def polynomial (z : List Bool) : MvPolynomial (Fin (arity z)) ℤ :=
  FormulaSignSlotRadialCenterValueCoefficient.polynomial (pairFst z) (order z) (radius z)
noncomputable def coefficient := FormulaSignSlotRadialCenterValueCoefficientNative.value

theorem arity_unary : UnaryFn arity := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialCenterValueLayout.original_FP)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterValuePacking.width_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialCenterValuePacking.degree_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterValueMass.budget_binary.comp pairFst_mem_FP
theorem evaluator : SpaceFunction coefficient := FormulaSignSlotRadialCenterValueCoefficientNative.evaluator

theorem polynomial_degree (z : List Bool) : (polynomial z).totalDegree ≤ degree z :=
  FormulaSignSlotRadialCenterValueCoefficient.degree _ _ _
theorem polynomial_mass (z : List Bool) : MvMass.mass (polynomial z) ≤ 2 ^ mass z :=
  by
  rw [polynomial, FormulaSignSlotRadialCenterValueCoefficient.polynomial_eq]
  exact (MvTwoParameterCoefficient.one_mass _ _).trans (FormulaSignSlotRadialCenterValueMass.mass _ _)
theorem fit (z : List Bool) : (polynomial z).totalDegree < 2 ^ width z := by
  exact (polynomial_degree z).trans_lt (FormulaSignSlotRadialCenterValuePacking.degree_fit (pairFst z))

theorem packet (z bits modulus : List Bool) : coefficient (pair (pair z bits) modulus) =
    residueBits ((((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
      (width z) (Nat.fromBitsLE bits))) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) :=
  FormulaSignSlotRadialCenterValueCoefficientNative.packet z bits modulus

end LeanCanny.Encoding.FormulaSignSlotRadialCenterValueSource

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalCoefficientNative
/-! # Original-only source metadata and coefficients for actual principal center tests

Context is the principal family context paired with order and radius degree.
The center variables remain formal integer variables throughout.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph

def order (z : List Bool) := Nat.fromBitsLE (pairFst (pairSnd z))
def radius (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
noncomputable def arity (z : List Bool) := d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (pairFst z)))
noncomputable def width (z : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.width (pairFst z)
noncomputable def degree (z : List Bool) := FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (pairFst z)
noncomputable def mass (z : List Bool) := FormulaSignSlotRadialCenterPrincipalMass.budget (pairFst z)
noncomputable def polynomial (z : List Bool) : MvPolynomial (Fin (arity z)) ℤ :=
  FormulaSignSlotRadialCenterPrincipalCoefficient.polynomial (pairFst z) (order z) (radius z)
noncomputable def coefficient := FormulaSignSlotRadialCenterPrincipalCoefficientNative.value

theorem arity_unary : UnaryFn arity := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialCenterPrincipalFamily.original_FP) pairFst_mem_FP)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterPrincipalFamily.width_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialCenterPrincipalFamily.degreeBound_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterPrincipalMass.budget_binary.comp pairFst_mem_FP
theorem evaluator : SpaceFunction coefficient := FormulaSignSlotRadialCenterPrincipalCoefficientNative.evaluator

theorem polynomial_degree (z : List Bool) : (polynomial z).totalDegree ≤ degree z :=
  FormulaSignSlotRadialCenterPrincipalCoefficient.degree _ _ _
theorem polynomial_mass (z : List Bool) : MvMass.mass (polynomial z) ≤ 2 ^ mass z :=
  FormulaSignSlotRadialCenterPrincipalCoefficient.mass _ _ _
theorem fit (z : List Bool) : (polynomial z).totalDegree < 2 ^ width z :=
  (MvTwoParameterCoefficient.one_degree _ _).trans_lt (FormulaSignSlotRadialCenterPrincipalFamily.principal_fit _ _)

theorem packet (z bits modulus : List Bool) : coefficient (pair (pair z bits) modulus) =
    residueBits ((((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
      (width z) (Nat.fromBitsLE bits))) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) :=
  FormulaSignSlotRadialCenterPrincipalCoefficientNative.packet z bits modulus

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalSource

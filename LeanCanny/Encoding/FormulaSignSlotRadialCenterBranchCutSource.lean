/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutCoefficientNative
/-! # Original-only source metadata and coefficients for actual actual branch-cut coefficients

Context is the branch family context paired with order and radius degree.
The center variables remain formal integer variables throughout.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower FixedWidthPolynomial
open LeanCanny.Connectivity.FormulaSignSlotCenteredRadialGraph

def order (z : List Bool) := Nat.fromBitsLE (pairFst (pairSnd z))
def radius (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
noncomputable def arity (z : List Bool) := d (pairFst (FormulaSignSlotRadialCenterPrincipalFamily.original (pairFst z)))
noncomputable def width (z : List Bool) := FormulaSignSlotRadialCenterBranchCutFamily.width (pairFst z)
noncomputable def degree (z : List Bool) := FormulaSignSlotRadialCenterBranchCutFamily.degreeBound (pairFst z)
noncomputable def mass (z : List Bool) := FormulaSignSlotRadialCenterBranchCutFamily.massBound (pairFst z)
noncomputable def polynomial (z : List Bool) : MvPolynomial (Fin (arity z)) ℤ :=
  FormulaSignSlotRadialCenterBranchCutCoefficient.polynomial (pairFst z) (order z) (radius z)
noncomputable def coefficient := FormulaSignSlotRadialCenterBranchCutCoefficientNative.value

theorem arity_unary : UnaryFn arity := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp (mem_FP_comp pairFst_mem_FP FormulaSignSlotRadialCenterPrincipalFamily.original_FP) pairFst_mem_FP)
theorem width_unary : UnaryFn width := FormulaSignSlotRadialCenterBranchCutFamily.width_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree := FormulaSignSlotRadialCenterBranchCutFamily.degreeBound_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterBranchCutFamily.massBound_binary.comp pairFst_mem_FP
theorem evaluator : SpaceFunction coefficient := FormulaSignSlotRadialCenterBranchCutCoefficientNative.evaluator

theorem polynomial_degree (z : List Bool) : (polynomial z).totalDegree ≤ degree z :=
  FormulaSignSlotRadialCenterBranchCutCoefficient.degree _ _ _
theorem polynomial_mass (z : List Bool) : MvMass.mass (polynomial z) ≤ 2 ^ mass z :=
  FormulaSignSlotRadialCenterBranchCutCoefficient.mass _ _ _
theorem fit (z : List Bool) : (polynomial z).totalDegree < 2 ^ width z := by
  apply (polynomial_degree z).trans_lt
  change FormulaSignSlotRadialCenterBranchCutFamily.degreeBound (pairFst z) <
    2 ^ (FormulaSignSlotRadialCenterBranchCutFamily.degreeBound (pairFst z)).size
  exact Nat.lt_size_self _

theorem packet (z bits modulus : List Bool) : coefficient (pair (pair z bits) modulus) =
    residueBits ((((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
      (width z) (Nat.fromBitsLE bits))) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) :=
  FormulaSignSlotRadialCenterBranchCutCoefficientNative.packet z bits modulus

end LeanCanny.Encoding.FormulaSignSlotRadialCenterBranchCutSource

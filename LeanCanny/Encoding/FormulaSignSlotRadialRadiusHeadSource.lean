/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadNative
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
/-! # A charged actual radius head with all center parameters retained

Context is pair eliminant-context (pair perturbation-word target-degree).
Radius and center remain literal integer variables. Large choices do not wrap.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity z := d (pairFst (pairFst z))+1
  width z := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (pairFst z)
  degree z := FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst z)
  mass z := FormulaSignSlotRadialEliminantFormalMass.budget (pairFst z)
  polynomial z := FormulaSignSlotRadialRadiusHead.polynomial (pairFst z) (Nat.fromBitsLE (pairFst (pairSnd z))) (Nat.fromBitsLE (pairSnd (pairSnd z)))
  fit _z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (FormulaSignSlotRadialRadiusHead.fit _ _ _)
  polynomial_degree _ := FormulaSignSlotRadialRadiusHead.degree _ _ _
  polynomial_mass _ := FormulaSignSlotRadialRadiusHead.mass _ _ _

private noncomputable def entry (z bits modulus : List Bool) :=
  residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
    (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1))
private theorem native_entry (q : List Bool) : FormulaSignSlotRadialRadiusHeadNative.value q =
    entry (RationalSubstitution.IntegerBits.context q) (RationalSubstitution.IntegerBits.selectedDegree q)
      (pairSnd q) := FormulaSignSlotRadialRadiusHeadNative.correct q
attribute [local irreducible] entry

theorem packet (z bits modulus : List Bool) :
    FormulaSignSlotRadialRadiusHeadNative.value (pair (pair z bits) modulus) =
      residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
        (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1)) := by
  rw [native_entry]
  simp only [RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair]
  unfold entry
  rfl

noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := ((FormulaSignSlotSource.dimension_unary.comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 1))
  width := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp pairFst_mem_FP
  degree := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp pairFst_mem_FP
  mass := FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp pairFst_mem_FP
  coefficient := FormulaSignSlotRadialRadiusHeadNative.value
  evaluator := FormulaSignSlotRadialRadiusHeadNative.evaluator
  packet := packet

end LeanCanny.Encoding.FormulaSignSlotRadialRadiusHeadSource

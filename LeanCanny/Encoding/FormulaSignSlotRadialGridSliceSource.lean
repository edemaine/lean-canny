/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialGridSliceNative
public import LeanCanny.Encoding.IntegralFramedBankPolynomialModel
/-! # A charged original grid-slice polynomial with all parameters retained

The context is pair eliminant-context perturbation-word. Target, radius,
and center remain literal integer variables. Large choices do not wrap.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialGridSliceSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def source : IntegralFramedBankPolynomialModel.Source where
  arity z := d (pairFst (pairFst z))+2
  width z := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (pairFst z)
  degree z := FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst z)
  mass z := FormulaSignSlotRadialEliminantFormalMass.budget (pairFst z)
  polynomial z := FormulaSignSlotRadialGridSlice.polynomial (pairFst z) (Nat.fromBitsLE (pairSnd z))
  fit _z i := (MvPolynomial.degreeOf_le_totalDegree _ i).trans_lt (FormulaSignSlotRadialGridSlice.fit _ _)
  polynomial_degree _ := FormulaSignSlotRadialGridSlice.degree _ _
  polynomial_mass _ := FormulaSignSlotRadialGridSlice.mass _ _

private noncomputable def entry (z bits modulus : List Bool) :=
  residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
    (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1))
private theorem native_entry (q : List Bool) : FormulaSignSlotRadialGridSliceNative.value q =
    entry (RationalSubstitution.IntegerBits.context q) (RationalSubstitution.IntegerBits.selectedDegree q)
      (pairSnd q) := FormulaSignSlotRadialGridSliceNative.correct q
attribute [local irreducible] entry

theorem packet (z bits modulus : List Bool) :
    FormulaSignSlotRadialGridSliceNative.value (pair (pair z bits) modulus) =
      residueBits (((source.polynomial z).coeff (nativeExponent (Equiv.refl _) (source.width z)
        (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus+1)) := by
  rw [native_entry]
  simp only [RationalSubstitution.IntegerBits.context,RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair,pairSnd_pair]
  unfold entry
  rfl

noncomputable def access : IntegralFramedBankPolynomialModel.Access source where
  arity := ((FormulaSignSlotSource.dimension_unary.comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)).add (UnaryFn.const 2))
  width := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp pairFst_mem_FP
  degree := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp pairFst_mem_FP
  mass := FormulaSignSlotRadialEliminantFormalMass.budget_binary.comp pairFst_mem_FP
  coefficient := FormulaSignSlotRadialGridSliceNative.value
  evaluator := FormulaSignSlotRadialGridSliceNative.evaluator
  packet := packet

end LeanCanny.Encoding.FormulaSignSlotRadialGridSliceSource

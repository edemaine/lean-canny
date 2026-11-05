/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientNative
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # Original-only degree, mass and native access for the same-center tests

The test datum contains the three coefficient indices. Changing that datum
never changes the original eliminant context or the retained center variables.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientSource
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower FixedWidthPolynomial
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialCenterCoefficient.polynomial

def selected (i : ℕ) (z : List Bool) := Nat.fromBitsLE (WordList.get (pairSnd z) i)
noncomputable def arity (z : List Bool) := d (pairFst (pairFst z))
noncomputable def oldWidth (z : List Bool) := FormulaSignSlotRadialEliminantPackingLayout.parameterWidth (pairFst z)
noncomputable def polynomial (z : List Bool) : MvPolynomial (Fin (arity z)) ℤ := FormulaSignSlotRadialCenterCoefficient.polynomial (pairFst z)
  (selected 0 z) (selected 1 z) (selected 2 z)
noncomputable def degree (z : List Bool) := FormulaSignSlotRadialEliminantPacked.resultDegree (pairFst z)
noncomputable def mass (z : List Bool) := FormulaSignSlotRadialCenterCoefficient.massBudget (pairFst z)
noncomputable def width (z : List Bool) := (degree z).size

theorem arity_unary : UnaryFn arity := FormulaSignSlotSource.dimension_unary.comp
  (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
theorem oldWidth_unary : UnaryFn oldWidth :=
  FormulaSignSlotRadialEliminantPackingLayout.parameterWidth_unary.comp pairFst_mem_FP
theorem degree_binary : BinaryFn degree :=
  FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp pairFst_mem_FP
theorem mass_binary : BinaryFn mass := FormulaSignSlotRadialCenterCoefficient.massBudget_binary.comp pairFst_mem_FP
theorem width_unary : UnaryFn width :=
  (UnaryFn.length degree_binary.bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
theorem polynomial_degree (z : List Bool) : (polynomial z).totalDegree ≤ degree z :=
  FormulaSignSlotRadialCenterCoefficient.degree _ _ _ _
theorem polynomial_mass (z : List Bool) : MvMass.mass (polynomial z) ≤ 2 ^ mass z :=
  FormulaSignSlotRadialCenterCoefficient.mass _ _ _ _
theorem old_fit (z : List Bool) : (polynomial z).totalDegree < 2 ^ oldWidth z :=
  (polynomial_degree z).trans_lt (FormulaSignSlotRadialEliminantPacked.result_fit _)

private noncomputable def entry (c indices bits modulus : List Bool) :=
  residueBits (((FormulaSignSlotRadialCenterCoefficient.polynomial c
    (Nat.fromBitsLE (WordList.get indices 0)) (Nat.fromBitsLE (WordList.get indices 1))
      (Nat.fromBitsLE (WordList.get indices 2))).coeff
        (nativeExponent (Equiv.refl (Fin (d (pairFst c))))
          (FormulaSignSlotRadialEliminantPackingLayout.parameterWidth c) (Nat.fromBitsLE bits)) : ℤ) :
            ZMod (Nat.fromBitsLE modulus + 1))

private theorem native_entry (q : List Bool) : FormulaSignSlotRadialCenterCoefficientNative.value q =
    entry (FormulaSignSlotRadialCenterCoefficientNative.origin q)
      (FormulaSignSlotRadialCenterCoefficientNative.indices q)
      (FormulaSignSlotRadialCenterCoefficientNative.target q) (pairSnd q) :=
  FormulaSignSlotRadialCenterCoefficientNative.correct q

attribute [local irreducible] entry

private theorem native_packet (z target modulus : List Bool) :
    FormulaSignSlotRadialCenterCoefficientNative.value (pair (pair z target) modulus) =
      residueBits (((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
        (oldWidth z) (Nat.fromBitsLE target)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [native_entry]
  simp only [FormulaSignSlotRadialCenterCoefficientNative.origin,
    FormulaSignSlotRadialCenterCoefficientNative.indices,
    FormulaSignSlotRadialCenterCoefficientNative.target,
    RationalSubstitution.IntegerBits.context, RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair, pairSnd_pair]
  unfold entry
  rfl

attribute [local irreducible] arity oldWidth degree width polynomial

def context := RationalSubstitution.IntegerBits.context
def target := RationalSubstitution.IntegerBits.selectedDegree
noncomputable def request (q : List Bool) := pair (pair (context q)
  (FixedWidthQuery.repack (arity ∘ context) (width ∘ context) (arity ∘ context) (oldWidth ∘ context) target q))
    (pairSnd q)
theorem context_FP : context ∈ FP := RationalSubstitution.IntegerBits.context_mem_FP
theorem target_FP : target ∈ FP := RationalSubstitution.IntegerBits.selectedDegree_mem_FP
theorem request_FP : request ∈ FP := mem_FP_pair (mem_FP_pair context_FP
  (FixedWidthQuery.repack_mem_FP (arity_unary.comp context_FP) (width_unary.comp context_FP)
    (arity_unary.comp context_FP) (oldWidth_unary.comp context_FP) target_FP)) pairSnd_mem_FP

noncomputable def coefficient : List Bool → List Bool :=
  FixedWidthRowBits.value (arity ∘ context) (width ∘ context) (fun q => polynomial (context q)) target pairSnd

theorem evaluator : SpaceFunction coefficient := by
  have E := FormulaSignSlotRadialCenterCoefficientNative.evaluator.precompose request request_FP
  have EO : SpaceFunction (FixedWidthRowBits.value (arity ∘ context) (oldWidth ∘ context)
      (fun q => polynomial (context q))
      (FixedWidthQuery.repack (arity ∘ context) (width ∘ context) (arity ∘ context) (oldWidth ∘ context) target) pairSnd) := by
    apply E.congr
    funext q
    simp only [Function.comp_apply]
    rw [request, native_packet]
    rfl
  exact FixedWidthRowReboxBits.evaluator (arity ∘ context) (oldWidth ∘ context) (width ∘ context)
    target (fun q => polynomial (context q)) pairSnd (arity_unary.comp context_FP) (oldWidth_unary.comp context_FP)
    (width_unary.comp context_FP) target_FP (fun q => old_fit (context q)) EO

private noncomputable def output (z bits modulus : List Bool) :=
  residueBits (((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
    (width z) (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1))

private theorem coefficient_output (q : List Bool) : coefficient q =
    output (context q) (target q) (pairSnd q) := rfl

attribute [local irreducible] output

theorem packet (z bits modulus : List Bool) : coefficient (pair (pair z bits) modulus) =
    residueBits (((polynomial z).coeff (nativeExponent (Equiv.refl (Fin (arity z)))
      (degree z).size (Nat.fromBitsLE bits)) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  rw [coefficient_output]
  simp only [context,
    RationalSubstitution.IntegerBits.context, target, RationalSubstitution.IntegerBits.selectedDegree,
    pairFst_pair, pairSnd_pair]
  unfold output width
  rfl

end LeanCanny.Encoding.FormulaSignSlotRadialCenterCoefficientSource

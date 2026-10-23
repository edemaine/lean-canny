/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeParameterCorrect
public import LeanCanny.Algebra.IndexedRationalSubstitutionBudget

/-! # Effective bounds for spatial coefficients after parameter substitution

The regular source provides its own coefficient allowance. Binary coordinate
bounds give FP output degree and coefficient-bit writers for every selected
spatial exponent, without an expanded coefficient polynomial or degree oracle.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeParameter
open LeanCanny.Encoding LeanCanny.Algebra
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm nativePolynomial

abbrev CoordinateBounds (source : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) :=
  IntegerBits.CoordinateBounds (fun c => parameterCount (source (pairFst c))) n d

-- Preserve the original qualified constructor and field names.
namespace CoordinateBounds
variable {source : List Bool → List Bool} {n d : List Bool → ℕ → Polynomial ℤ}

abbrev mk := @IntegerBits.CoordinateBounds.mk (fun c => parameterCount (source (pairFst c))) n d
abbrev degree (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.degree self
abbrev bits (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.bits self
abbrev degreeFP (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.degreeFP self
abbrev bitsFP (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.bitsFP self
abbrev numerator_degree (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.numerator_degree self
abbrev denominator_degree (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.denominator_degree self
abbrev numerator_coeff (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.numerator_coeff self
abbrev denominator_coeff (self : CoordinateBounds source n d) := IntegerBits.CoordinateBounds.denominator_coeff self

end CoordinateBounds

def sourceBits (source : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNatCode.encode (TubeRegularSource.coefficientBudget (source (pairFst c)))

theorem sourceBits_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : sourceBits source ∈ FP :=
  bits_mem_FP ((TubeRegularSource.coefficientBudget_unary.comp hs).comp pairFst_mem_FP)

theorem source_coefficient_bound (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    (coefficient source active row c r).natAbs ≤ 2 ^ Nat.fromBitsLE (sourceBits source c) := by
  simp only [sourceBits, Algebra.MacaulayBits.fromBits_encode]
  unfold coefficient
  split_ifs
  · unfold nativeCoefficient nativePolynomial
    exact TubeRegularHomogenization.coefficient_bound _ _ _ _
  · exact Nat.zero_le _

noncomputable def degreeCode (source coordinateDegree : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.degreeCode (arityCode source c) (widthCode source c) (coordinateDegree c)

noncomputable def budgetCode (source coordinateDegree coordinateBits : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.coefficientBudgetCode (arityCode source c) (widthCode source c) (termsCode source c)
    (coordinateDegree c) (coordinateBits c) (sourceBits source c)

theorem degreeCode_mem_FP {source coordinateDegree : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) : degreeCode source coordinateDegree ∈ FP :=
  (sourceAccess source id id).outputDegreeCode_mem_FP (arityCode_mem_FP hs) (widthCode_mem_FP hs) hE

theorem budgetCode_mem_FP {source coordinateDegree coordinateBits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) (hb : coordinateBits ∈ FP) : budgetCode source coordinateDegree coordinateBits ∈ FP :=
  (sourceAccess source id id).outputBudgetCode_mem_FP
    (arityCode_mem_FP hs) (widthCode_mem_FP hs) (termsCode_mem_FP hs) hE hb (sourceBits_mem_FP hs)

theorem polynomial_degree (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : CoordinateBounds source n d) (c : List Bool) :
    ((family source active row n d).polynomial c).natDegree ≤ Nat.fromBitsLE (degreeCode source B.degree c) :=
  (sourceAccess source active row).polynomial_degree B c

theorem polynomial_coefficient_bits (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : CoordinateBounds source n d) (c : List Bool) (k : ℕ) :
    (((family source active row n d).polynomial c).coeff k).natAbs.size ≤
      Nat.fromBitsLE (budgetCode source B.degree B.bits c) :=
  (sourceAccess source active row).polynomial_coefficient_bits B (sourceBits source)
    (fun c r _ => source_coefficient_bound source active row c r) c k

end LeanCanny.ETR.TubeParameter

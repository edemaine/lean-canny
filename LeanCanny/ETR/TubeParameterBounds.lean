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

structure CoordinateBounds (source : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) where
  degree : List Bool → List Bool
  bits : List Bool → List Bool
  degreeFP : degree ∈ FP
  bitsFP : bits ∈ FP
  numerator_degree : ∀ c i, i < parameterCount (source (pairFst c)) → (n c i).natDegree ≤ Nat.fromBitsLE (degree c)
  denominator_degree : ∀ c i, i < parameterCount (source (pairFst c)) → (d c i).natDegree ≤ Nat.fromBitsLE (degree c)
  numerator_coeff : ∀ c i, i < parameterCount (source (pairFst c)) → ∀ k, ((n c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)
  denominator_coeff : ∀ c i, i < parameterCount (source (pairFst c)) → ∀ k, ((d c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)

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
  Indexed.degreeCode_mem_FP (arityCode_mem_FP hs) (widthCode_mem_FP hs) hE

theorem budgetCode_mem_FP {source coordinateDegree coordinateBits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) (hb : coordinateBits ∈ FP) : budgetCode source coordinateDegree coordinateBits ∈ FP :=
  Indexed.coefficientBudgetCode_mem_FP (arityCode_mem_FP hs) (widthCode_mem_FP hs) (termsCode_mem_FP hs)
    hE hb (sourceBits_mem_FP hs)

theorem polynomial_degree (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : CoordinateBounds source n d) (c : List Bool) :
    ((family source active row n d).polynomial c).natDegree ≤ Nat.fromBitsLE (degreeCode source B.degree c) := by
  simp only [degreeCode, Indexed.degreeCode_code, Algebra.MacaulayBits.fromBits_encode, arityCode, widthCode,
    Function.comp_apply, TubeIndexed.clearingWidthCode_code]
  exact Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _ ((family source active row n d).exponent_le c)
    (B.numerator_degree c) (B.denominator_degree c)

theorem polynomial_coefficient_bits (source active row : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
    (B : CoordinateBounds source n d) (c : List Bool) (k : ℕ) :
    (((family source active row n d).polynomial c).coeff k).natAbs.size ≤
      Nat.fromBitsLE (budgetCode source B.degree B.bits c) := by
  simp only [budgetCode, Indexed.coefficientBudgetCode_code, arityCode, widthCode, termsCode, Function.comp_apply,
    TubeIndexed.clearingWidthCode_code, FixedWidthPolynomial.countCode_code, Algebra.MacaulayBits.fromBits_encode]
  exact Indexed.coeff_size_cleared_le _ _ _ _ _ _ _ _ _ ((family source active row n d).exponent_le c)
    (fun r _ => source_coefficient_bound source active row c r)
    (fun i hi => Algebra.coefficientMass_le_pow_of_degree_coeff _ _ _ (B.numerator_degree c i hi) (B.numerator_coeff c i hi))
    (fun i hi => Algebra.coefficientMass_le_pow_of_degree_coeff _ _ _ (B.denominator_degree c i hi) (B.denominator_coeff c i hi)) k

end LeanCanny.ETR.TubeParameter

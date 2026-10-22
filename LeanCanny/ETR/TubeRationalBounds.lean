/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeRationalSubstitution
public import LeanCanny.Algebra.IndexedRationalSubstitutionBudget

/-! # Effective output bounds for rational tube substitution

Coordinate degree and coefficient-bit writers suffice. The actual tube or
projection source supplies its own coefficient budget; callers do not assume
source coefficient bounds or an actual output degree oracle.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeRational

open LeanCanny.Encoding
open Geometry TubeEncoding
open Algebra.RationalSubstitution

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubePolynomial.integerPolynomial
  TubePolynomial.integerProjection TubeProjection.decodedRow

structure CoordinateBounds (projection : Bool) (source : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) where
  degree : List Bool → List Bool
  bits : List Bool → List Bool
  degreeFP : degree ∈ FP
  bitsFP : bits ∈ FP
  numerator_degree : ∀ c i, i < dimension projection (source c) → (n c i).natDegree ≤ Nat.fromBitsLE (degree c)
  denominator_degree : ∀ c i, i < dimension projection (source c) → (d c i).natDegree ≤ Nat.fromBitsLE (degree c)
  numerator_coeff : ∀ c i, i < dimension projection (source c) → ∀ k, ((n c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)
  denominator_coeff : ∀ c i, i < dimension projection (source c) → ∀ k, ((d c i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (bits c)

def sourceBits (source : List Bool → List Bool) : List Bool → List Bool := TubeSource.coefficientBits ∘ source

theorem sourceBits_mem_FP {source : List Bool → List Bool} (hs : source ∈ FP) : sourceBits source ∈ FP :=
  mem_FP_comp hs TubeSource.coefficientBits_FP

theorem source_coefficient_bound (projection : Bool) (source active row : List Bool → List Bool) (c : List Bool) (r : ℕ) :
    (coefficient projection source active row c r).natAbs ≤ 2 ^ Nat.fromBitsLE (sourceBits source c) := by
  have h : (coefficient projection source active row c r).natAbs ≤ 2 ^ TubeSource.massBudget (CompactSource.size (source c)) := by
    cases projection
    · exact TubeIndexed.tubeCoefficient_mass (source c) _ r
    · exact TubeIndexed.projectionCoefficient_mass (source c) _ _ r
  apply h.trans
  apply Nat.pow_le_pow_right (by decide)
  simp only [sourceBits, Function.comp_apply, TubeSource.coefficientBits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  omega

noncomputable def degreeCode (projection : Bool) (source coordinateDegree : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.degreeCode (arityCode projection source c) (widthCode source c) (coordinateDegree c)

noncomputable def budgetCode (projection : Bool) (source coordinateDegree coordinateBits : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.coefficientBudgetCode (arityCode projection source c) (widthCode source c) (termsCode projection source c)
    (coordinateDegree c) (coordinateBits c) (sourceBits source c)

theorem degreeCode_mem_FP (projection : Bool) {source coordinateDegree : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) : degreeCode projection source coordinateDegree ∈ FP :=
  Indexed.degreeCode_mem_FP (arityCode_mem_FP projection hs) (widthCode_mem_FP hs) hE

theorem budgetCode_mem_FP (projection : Bool) {source coordinateDegree coordinateBits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) (hb : coordinateBits ∈ FP) : budgetCode projection source coordinateDegree coordinateBits ∈ FP :=
  Indexed.coefficientBudgetCode_mem_FP (arityCode_mem_FP projection hs) (widthCode_mem_FP hs) (termsCode_mem_FP projection hs)
    hE hb (sourceBits_mem_FP hs)

theorem polynomial_degree (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (B : CoordinateBounds projection source n d) (c : List Bool) :
    ((family projection source active row n d).polynomial c).natDegree ≤ Nat.fromBitsLE (degreeCode projection source B.degree c) := by
  simp only [degreeCode, Indexed.degreeCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits, arityCode_eq, widthCode_eq]
  exact Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _ ((family projection source active row n d).exponent_le c)
    (B.numerator_degree c) (B.denominator_degree c)

theorem polynomial_coefficient_bits (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (B : CoordinateBounds projection source n d) (c : List Bool) (k : ℕ) :
    (((family projection source active row n d).polynomial c).coeff k).natAbs.size ≤
      Nat.fromBitsLE (budgetCode projection source B.degree B.bits c) := by
  simp only [budgetCode, Indexed.coefficientBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    arityCode_eq, widthCode_eq, termsCode_eq]
  exact Indexed.coeff_size_cleared_le _ _ _ _ _ _ _ _ _ ((family projection source active row n d).exponent_le c)
    (fun r _ => source_coefficient_bound projection source active row c r)
    (fun i hi => Algebra.coefficientMass_le_pow_of_degree_coeff _ _ _ (B.numerator_degree c i hi) (B.numerator_coeff c i hi))
    (fun i hi => Algebra.coefficientMass_le_pow_of_degree_coeff _ _ _ (B.denominator_degree c i hi) (B.denominator_coeff c i hi)) k

end LeanCanny.ETR.TubeRational

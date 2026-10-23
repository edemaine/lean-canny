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

abbrev CoordinateBounds (projection : Bool) (source : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) :=
  IntegerBits.CoordinateBounds (fun c => dimension projection (source c)) n d

-- Preserve the original qualified constructor and field names.
namespace CoordinateBounds
variable {projection : Bool} {source : List Bool → List Bool} {n d : List Bool → ℕ → Polynomial ℤ}

abbrev mk := @IntegerBits.CoordinateBounds.mk (fun c => dimension projection (source c)) n d
abbrev degree (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.degree self
abbrev bits (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.bits self
abbrev degreeFP (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.degreeFP self
abbrev bitsFP (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.bitsFP self
abbrev numerator_degree (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.numerator_degree self
abbrev denominator_degree (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.denominator_degree self
abbrev numerator_coeff (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.numerator_coeff self
abbrev denominator_coeff (self : CoordinateBounds projection source n d) := IntegerBits.CoordinateBounds.denominator_coeff self

end CoordinateBounds

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
  (sourceAccess projection source id id).outputDegreeCode_mem_FP (arityCode_mem_FP projection hs) (widthCode_mem_FP hs) hE

theorem budgetCode_mem_FP (projection : Bool) {source coordinateDegree coordinateBits : List Bool → List Bool}
    (hs : source ∈ FP) (hE : coordinateDegree ∈ FP) (hb : coordinateBits ∈ FP) : budgetCode projection source coordinateDegree coordinateBits ∈ FP :=
  (sourceAccess projection source id id).outputBudgetCode_mem_FP
    (arityCode_mem_FP projection hs) (widthCode_mem_FP hs) (termsCode_mem_FP projection hs) hE hb (sourceBits_mem_FP hs)

theorem polynomial_degree (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (B : CoordinateBounds projection source n d) (c : List Bool) :
    ((family projection source active row n d).polynomial c).natDegree ≤ Nat.fromBitsLE (degreeCode projection source B.degree c) :=
  (sourceAccess projection source active row).polynomial_degree B c

theorem polynomial_coefficient_bits (projection : Bool) (source active row : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (B : CoordinateBounds projection source n d) (c : List Bool) (k : ℕ) :
    (((family projection source active row n d).polynomial c).coeff k).natAbs.size ≤
      Nat.fromBitsLE (budgetCode projection source B.degree B.bits c) :=
  (sourceAccess projection source active row).polynomial_coefficient_bits B (sourceBits source)
    (fun c r _ => source_coefficient_bound projection source active row c r) c k

end LeanCanny.ETR.TubeRational

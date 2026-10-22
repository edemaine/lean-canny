/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveSymbolicSampling
public import LeanCanny.Algebra.SymbolicFixedTableSignBounds
public import LeanCanny.Algebra.CoerciveQueryBounds

/-! # Native binary bounds for the final prepared root and cleared sign queries -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSymbolicBounds
open LeanCanny.Algebra LeanCanny.Encoding
open CoerciveSourceSampling CoerciveSourceControls CoercivePreparationControls CoerciveSymbolicSampling
open Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix

noncomputable def sourceHeight (bits : List Bool) : ℕ :=
  CoerciveQuerySystem.height (dimension bits) (degreeAllowance bits) (massAllowance bits) (penaltyExponent bits)

noncomputable def queryDegree (bits : List Bool) : ℕ :=
  2 * (dimension bits + 1) * allowance bits * referenceExponent bits

noncomputable def queryMassExponent (bits : List Bool) : ℕ := sourceHeight bits + queryDegree bits

private theorem unary_binary {f : List Bool → ℕ} (hf : UnaryFn f) : BinaryFn f :=
  BinaryFn.of_bits (bits_mem_FP hf)

theorem allowance_unary : UnaryFn allowance :=
  ((UnaryFn.const 2).mul degreeAllowance_unary).add (UnaryFn.const 2)

theorem sourceHeight_binary : BinaryFn sourceHeight :=
  (((penaltyExponent_binary.add ((unary_binary degreeAllowance_unary.size).add
    ((BinaryFn.const 2).mul (unary_binary massAllowance_unary)) |>.add (BinaryFn.const 3))).add
      (unary_binary dimension_unary.size)).add (BinaryFn.const 1))

theorem queryDegree_binary : BinaryFn queryDegree :=
  (((BinaryFn.const 2).mul (unary_binary (dimension_unary.add (UnaryFn.const 1)))).mul
    (unary_binary allowance_unary)).mul referenceExponent_binary

theorem queryMassExponent_binary : BinaryFn queryMassExponent := sourceHeight_binary.add queryDegree_binary

theorem integerQuery_mass (bits : List Bool) (j : Query bits) :
    MvMass.mass (integerQuery bits j) ≤ 2 ^ sourceHeight bits := by
  rcases j with i | b
  · exact CoerciveQuerySystem.gradient_mass_le_pow _ _ _ _ (polynomial_degree bits) (polynomial_mass bits) i
  · cases b
    · exact CoerciveQuerySystem.bound_mass_le_pow _ _ _
    · exact CoerciveQuerySystem.residual_mass_le_pow _ _ _ _ (polynomial_mass bits)

theorem source_mass (bits : List Bool) (j : Query bits) :
    BivariateRationalSubstitution.sourceMass (query bits j) ≤ 2 ^ sourceHeight bits := by
  rw [query, BivariateRationalSubstitution.sourceMass_map_int]
  exact integerQuery_mass bits j

theorem cleared_degree (bits : List Bool) (j : Query bits) :
    (clearedQuery bits j).natDegree ≤ queryDegree bits := by
  exact (family bits).signQueryWith_degree (allowance bits) (query bits j) (query_degree bits j)

theorem cleared_inner_degree (bits : List Bool) (j : Query bits) (k : ℕ) :
    ((clearedQuery bits j).coeff k).natDegree ≤ queryDegree bits := by
  have hp (e) : ((query bits j).coeff e).natDegree ≤ 0 := by
    rw [query, MvPolynomial.coeff_map]
    change (Polynomial.C ((integerQuery bits j).coeff e)).natDegree ≤ 0
    simp only [natDegree_C, le_refl]
  exact ((family bits).signQueryWith_inner_degree (allowance bits) 0 (query bits j)
    (query_degree bits j) hp k).trans_eq (Nat.zero_add _)

theorem cleared_mass (bits : List Bool) (j : Query bits) :
    NestedMass.mass (clearedQuery bits j) ≤ 2 ^ queryMassExponent bits := by
  exact (family bits).signQueryWith_mass (allowance bits) (sourceHeight bits) (query bits j)
    (query_degree bits j) (source_mass bits j)

theorem parameter_degree (bits : List Bool) : (family bits).parameter.natDegree ≤ referenceExponent bits :=
  (family bits).parameter_controls.1

theorem parameter_inner_degree (bits : List Bool) (k : ℕ) :
    ((family bits).parameter.coeff k).natDegree ≤ referenceExponent bits :=
  (family bits).parameter_controls.2.1 k

theorem parameter_mass (bits : List Bool) :
    NestedMass.mass (family bits).parameter ≤ 2 ^ (2 * referenceExponent bits + 1) :=
  (family bits).parameter_mass

end LeanCanny.ETR.CoerciveSymbolicBounds

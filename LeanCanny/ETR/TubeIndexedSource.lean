/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.ETR.TubeSourceProjectionCoefficient

/-! # Indexed monomial sources for the actual tube and projection polynomials

The block width is the binary size of the proved full degree allowance. Binary
ranks enumerate all such exponent vectors, and their coefficients are the actual
collected native coefficients. FP metadata writers give the variable counts,
exponent blocks, and binary term counts without expanding the polynomials.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeIndexed

open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.RationalSubstitution.Indexed

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def degreeBound (bits : List Bool) : ℕ := 8 * CompactSource.size bits ^ 2 + 4

def blockWidth (bits : List Bool) : ℕ := (degreeBound bits).size

noncomputable def arity (bits : List Bool) : ℕ := (CompactSource.term bits).arity

noncomputable def tubeDimension (bits : List Bool) : ℕ := TubeEncoding.dimension (arity bits)
noncomputable def projectionDimension (bits : List Bool) : ℕ := TubeProjectionEncoding.dimension (arity bits)

theorem degreeBound_unary : UnaryFn degreeBound :=
  ((UnaryFn.const 8).mul (CompactSource.size_unary.pow_const 2)).add (UnaryFn.const 4)

theorem blockWidth_unary : UnaryFn blockWidth := degreeBound_unary.size

theorem arity_unary : UnaryFn arity := TubeDense.arity_unary RationalSubstitutionBits.compiledTerm_mem_FP

theorem tubeDimension_unary : UnaryFn tubeDimension := TubeZeroQuery.dimension_unary arity_unary

theorem projectionDimension_unary : UnaryFn projectionDimension := TubeProjectionQuery.dimension_unary arity_unary

theorem degreeBound_lt (bits : List Bool) : degreeBound bits < 2 ^ blockWidth bits := Nat.lt_size_self _

noncomputable def tubeExponent (bits : List Bool) (r : ℕ) : Coordinate (arity bits) →₀ ℕ :=
  Algebra.FixedWidthPolynomial.nativeExponent (coordinateEquiv (arity bits)) (blockWidth bits) r

noncomputable def projectionExponent (bits : List Bool) (r : ℕ) : Variable (arity bits) →₀ ℕ :=
  Algebra.FixedWidthPolynomial.nativeExponent (variableEquiv (arity bits)) (blockWidth bits) r

noncomputable def tubeCoefficient (bits : List Bool) (s : Finset (Constraint (arity bits))) (r : ℕ) : ℤ :=
  (TubeSource.integerPolynomial bits s).coeff (tubeExponent bits r)

noncomputable def projectionCoefficient (bits : List Bool) (s : Finset (Constraint (arity bits)))
    (j : TubeSource.ProjectionIndex bits) (r : ℕ) : ℤ :=
  (TubeSource.integerProjection bits s j).coeff (projectionExponent bits r)

noncomputable def tubeCountCode : List Bool → List Bool := Algebra.FixedWidthPolynomial.countCode tubeDimension blockWidth
noncomputable def projectionCountCode : List Bool → List Bool := Algebra.FixedWidthPolynomial.countCode projectionDimension blockWidth

theorem tubeCountCode_mem_FP : tubeCountCode ∈ FP := Algebra.FixedWidthPolynomial.countCode_mem_FP tubeDimension_unary blockWidth_unary

theorem projectionCountCode_mem_FP : projectionCountCode ∈ FP := Algebra.FixedWidthPolynomial.countCode_mem_FP projectionDimension_unary blockWidth_unary

theorem tubeExponentRead_mem_FP : Algebra.FixedWidthPolynomial.exponentRead tubeDimension blockWidth ∈ FP :=
  Algebra.FixedWidthPolynomial.exponentRead_mem_FP tubeDimension_unary blockWidth_unary

theorem projectionExponentRead_mem_FP : Algebra.FixedWidthPolynomial.exponentRead projectionDimension blockWidth ∈ FP :=
  Algebra.FixedWidthPolynomial.exponentRead_mem_FP projectionDimension_unary blockWidth_unary

theorem tube_source_eq (bits : List Bool) (s : Finset (Constraint (arity bits))) :
    source (tubeDimension bits) (Algebra.FixedWidthPolynomial.count (tubeDimension bits) (blockWidth bits))
      (tubeCoefficient bits s) (Algebra.FixedWidthPolynomial.entry (blockWidth bits)) =
        MvPolynomial.rename (coordinateEquiv (arity bits)) (TubeSource.integerPolynomial bits s) := by
  have hd := TubeSource.integer_polynomial_degree_le_code bits s
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hd
  exact Algebra.FixedWidthPolynomial.indexed_source_eq_rename _ _ (blockWidth bits) (degreeBound bits) hd (degreeBound_lt bits)

theorem projection_source_eq (bits : List Bool) (s : Finset (Constraint (arity bits))) (j : TubeSource.ProjectionIndex bits) :
    source (projectionDimension bits) (Algebra.FixedWidthPolynomial.count (projectionDimension bits) (blockWidth bits))
      (projectionCoefficient bits s j) (Algebra.FixedWidthPolynomial.entry (blockWidth bits)) =
        MvPolynomial.rename (variableEquiv (arity bits)) (TubeSource.integerProjection bits s j) := by
  have hd := TubeSource.integer_projection_degree_le_code bits s j
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hd
  exact Algebra.FixedWidthPolynomial.indexed_source_eq_rename _ _ (blockWidth bits) (degreeBound bits) hd (degreeBound_lt bits)

end LeanCanny.ETR.TubeIndexed

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CriticalPointSource
public import LeanCanny.ETR.RadiusSource
public import LeanCanny.Geometry.TubeExpanded

/-! # Active tube projection systems for every encoded ETR input

The tube and its projection system are provided both over Z[epsilon,delta,alpha]
and as ordinary integer polynomials. All fixed epsilon and delta admit a common
interval of regular positive alpha levels. Equation count, variable count, and
total degree have FP upper-bound writers, including the parameter block in the
integer representation. Coefficient access, finite sampling, and effective
alpha selection remain separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSource

open LeanCanny.Encoding
open Geometry

abbrev Coordinate (bits : List Bool) := TubePolynomial.Coordinate (Fin (CompactSource.term bits).arity)
abbrev ProjectionIndex (bits : List Bool) := TubePolynomial.ProjectionIndex (Fin (CompactSource.term bits).arity)
abbrev IntegerProjectionVariable (bits : List Bool) := TubePolynomial.IntegerProjectionVariable (Fin (CompactSource.term bits).arity)

noncomputable def polynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    MvPolynomial (Coordinate bits) TubePolynomial.Coefficient :=
  TubePolynomial.polynomial (CompactSource.polynomial bits) s

noncomputable def projectionSystem (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : ProjectionIndex bits) :
    MvPolynomial (Algebra.ProjectionEquations.Variable (Coordinate bits)) TubePolynomial.Coefficient :=
  TubePolynomial.projectionSystem (CompactSource.polynomial bits) s j

noncomputable def integerPolynomial (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :=
  TubePolynomial.integerPolynomial (CompactSource.polynomial bits) s

noncomputable def integerProjection (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : ProjectionIndex bits) :
    MvPolynomial (IntegerProjectionVariable bits) ℤ :=
  TubePolynomial.integerProjection (CompactSource.polynomial bits) s j

theorem zero_level_iff (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (epsilon delta : ℝ) (z : PerturbedSource.Point bits) :
    (polynomial bits s).eval₂ (TubePolynomial.coefficientMap epsilon delta 0) (TubePolynomial.point z) = 0 ↔
      SquaredRadius.value z.2 = delta ^ 2 ∧
        ∀ i ∈ s, PolynomialPerturbation.parameterMap (CompactSource.polynomial bits) epsilon z i = 0 :=
  TubePolynomial.zero_level_iff _ _ _ _ _

theorem exists_regular_interval (bits : List Bool) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ (s : Finset (PerturbedSource.Index bits)) (x : Coordinate bits → ℝ),
        (polynomial bits s).eval₂ (TubePolynomial.coefficientMap epsilon delta alpha) x = 0 →
        Function.Surjective (fderiv ℝ (fun y => (polynomial bits s).eval₂
          (TubePolynomial.coefficientMap epsilon delta alpha) y) x) :=
  TubePolynomial.exists_common_regular_interval _ _ _

theorem exists_projection_interval (bits : List Bool) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ TubePolynomial.ProjectionInterval (CompactSource.polynomial bits) epsilon delta a :=
  TubePolynomial.exists_projectionInterval (CompactSource.polynomial bits) epsilon delta

theorem exists_integer_projection_interval (bits : List Bool) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ TubePolynomial.IntegerProjectionInterval (CompactSource.polynomial bits) epsilon delta a :=
  TubePolynomial.exists_integer_projection_interval (CompactSource.polynomial bits) epsilon delta

theorem eval_integerProjection (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) (j : ProjectionIndex bits)
    (epsilon delta alpha : ℝ) (x v : Coordinate bits → ℝ) :
    (integerProjection bits s j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim (Sum.elim x v) (TubePolynomial.parameters epsilon delta alpha)) =
      (projectionSystem bits s j).eval₂ (TubePolynomial.coefficientMap epsilon delta alpha) (Sum.elim x v) :=
  TubePolynomial.eval_integerProjection _ _ _ _ _ _ _ _

def countCode (bits : List Bool) : List Bool := BinaryNatCode.encode (2 + 3 * CompactSource.size bits)
def dimensionCode (bits : List Bool) : List Bool := BinaryNatCode.encode (4 + 6 * CompactSource.size bits)
def integerDimensionCode (bits : List Bool) : List Bool := BinaryNatCode.encode (7 + 6 * CompactSource.size bits)

theorem countCode_FP : countCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 2).add ((UnaryFn.const 3).mul CompactSource.size_unary))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem dimensionCode_FP : dimensionCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 4).add ((UnaryFn.const 6).mul CompactSource.size_unary))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem integerDimensionCode_FP : integerDimensionCode ∈ FP := by
  have h := bits_mem_FP ((UnaryFn.const 7).add ((UnaryFn.const 6).mul CompactSource.size_unary))
  exact mem_FP_of_eq h (fun _ => rfl)

theorem count_le_code (bits : List Bool) : Fintype.card (ProjectionIndex bits) ≤ Nat.fromBitsLE (countCode bits) := by
  have h := TubePolynomial.projection_count (ι := Fin (CompactSource.term bits).arity)
  have ha := (CompactSource.term bits).arity_le_dataSize
  simp only [Fintype.card_fin] at h
  simp only [countCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  rw [h]
  omega

theorem dimension_le_code (bits : List Bool) :
    Fintype.card (Algebra.ProjectionEquations.Variable (Coordinate bits)) ≤ Nat.fromBitsLE (dimensionCode bits) := by
  have h := TubePolynomial.projection_variable_count (ι := Fin (CompactSource.term bits).arity)
  have ha := (CompactSource.term bits).arity_le_dataSize
  simp only [Fintype.card_fin] at h
  simp only [dimensionCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  rw [h]
  omega

theorem integer_dimension_le_code (bits : List Bool) :
    Fintype.card (IntegerProjectionVariable bits) ≤ Nat.fromBitsLE (integerDimensionCode bits) := by
  have h := TubePolynomial.integer_projection_variable_count (ι := Fin (CompactSource.term bits).arity)
  have ha := (CompactSource.term bits).arity_le_dataSize
  simp only [Fintype.card_fin] at h
  simp only [integerDimensionCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  rw [h]
  omega

theorem polynomial_degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (polynomial bits s).totalDegree ≤ Nat.fromBitsLE (RadiusSource.degreeCode bits) := by
  have h := TubePolynomial.polynomial_degree (CompactSource.polynomial bits) s
  have hp := CompactSource.polynomial_degree bits
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

theorem projection_degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : ProjectionIndex bits) :
    (projectionSystem bits s j).totalDegree ≤ Nat.fromBitsLE (RadiusSource.degreeCode bits) := by
  have h := TubePolynomial.projection_degree (CompactSource.polynomial bits) s j
  have hp := CompactSource.polynomial_degree bits
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

theorem integer_polynomial_degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits)) :
    (integerPolynomial bits s).totalDegree ≤ Nat.fromBitsLE (RadiusSource.degreeCode bits) := by
  have h := TubePolynomial.integer_polynomial_degree (CompactSource.polynomial bits) s
  have hp := CompactSource.polynomial_degree bits
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

theorem integer_projection_degree_le_code (bits : List Bool) (s : Finset (PerturbedSource.Index bits))
    (j : ProjectionIndex bits) :
    (integerProjection bits s j).totalDegree ≤ Nat.fromBitsLE (RadiusSource.degreeCode bits) := by
  have h := TubePolynomial.integer_projection_degree (CompactSource.polynomial bits) s j
  have hp := CompactSource.polynomial_degree bits
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits, CompactSource.size_eq]
  exact h.trans (by omega)

end LeanCanny.ETR.TubeSource

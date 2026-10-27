/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalFilterCoefficients

/-! # Native degree and coefficient-mass controls for critical-sample filters -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalFilterBounds
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open BoundedCriticalFilterCoefficients RationalSubstitution.Indexed
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate

noncomputable def terms (P : Readers) (c : List Bool) : ℕ :=
  FixedWidthPolynomial.count (P.dim c + 4) (BoundedCriticalProjection.systemWidth P c)

theorem terms_binary {P : Readers} (h : P.PolyTime) : BinaryFn (terms P) := by
  apply BinaryFn.of_bits
  apply mem_FP_of_eq (FixedWidthPolynomial.countCode_mem_FP (h.dim.add (UnaryFn.const 4))
    (BoundedCriticalProjection.systemWidth_unary h))
  intro c
  exact FixedWidthPolynomial.countCode_code _ _ c

noncomputable def degree (P : Readers) (c : List Bool) : ℕ :=
  (P.dim c + 4) * (2 * BoundedCriticalFilters.gridDegree P c) * BoundedCriticalRationalCoordinates.coordinateDegree P c
noncomputable def mass (P : Readers) (c : List Bool) : ℕ :=
  (terms P c).size + BoundedCriticalProjection.equationBits P c +
    (P.dim c + 4) * (2 * BoundedCriticalFilters.gridDegree P c) * BoundedCriticalRationalCoordinates.coordinateMass P c

theorem degree_binary {P : Readers} (h : P.PolyTime) : BinaryFn (degree P) :=
  ((BinaryFn.ofUnary (h.dim.add (UnaryFn.const 4))).mul
    ((BinaryFn.const 2).mul (BoundedCriticalFilters.gridDegree_binary h))).mul
      (BoundedCriticalRationalCoordinates.coordinateDegree_binary h)
theorem mass_binary {P : Readers} (h : P.PolyTime) : BinaryFn (mass P) :=
  (((terms_binary h).size).add (BoundedCriticalProjection.equationBits_binary h)).add
    (((BinaryFn.ofUnary (h.dim.add (UnaryFn.const 4))).mul
      ((BinaryFn.const 2).mul (BoundedCriticalFilters.gridDegree_binary h))).mul
        (BoundedCriticalRationalCoordinates.coordinateMass_binary h))

theorem coordinate_bounds (P : Readers) (c : List Bool) (i : ℕ) :
    (BoundedCriticalFilters.numerator P c i).natDegree ≤ BoundedCriticalRationalCoordinates.coordinateDegree P c ∧
      (BoundedCriticalFilters.denominator P c i).natDegree ≤ BoundedCriticalRationalCoordinates.coordinateDegree P c ∧
      coefficientMass (BoundedCriticalFilters.numerator P c i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P c ∧
      coefficientMass (BoundedCriticalFilters.denominator P c i) ≤ 2 ^ BoundedCriticalRationalCoordinates.coordinateMass P c := by
  have H := BoundedCriticalRationalCoordinates.coordinate_bounds P (pair c (BinaryNatCode.encode i))
  simp only [pairFst_pair] at H
  exact ⟨(le_max_left _ _).trans H.1, (le_max_right _ _).trans H.1, H.2.1, H.2.2⟩

theorem polynomial_degree (P : Readers) (w : List Bool) :
    (BoundedCriticalFilters.polynomial P w).natDegree ≤ degree P (pairFst w) := by
  rw [← polynomial_eq]
  exact natDegree_cleared_le (arity P w) (terms P (pairFst w))
    (2 * BoundedCriticalFilters.gridDegree P (pairFst w))
    (BoundedCriticalRationalCoordinates.coordinateDegree P (pairFst w))
    (sourceCoefficient P w) (FixedWidthPolynomial.entry (width P w))
    (BoundedCriticalFilters.numerator P (pairFst w)) (BoundedCriticalFilters.denominator P (pairFst w))
    ((family P).exponent_le w) (fun i _ => (coordinate_bounds P (pairFst w) i).1)
    (fun i _ => (coordinate_bounds P (pairFst w) i).2.1)

theorem polynomial_mass (P : Readers) (w : List Bool) :
    coefficientMass (BoundedCriticalFilters.polynomial P w) ≤ 2 ^ mass P (pairFst w) := by
  rw [← polynomial_eq]
  exact coefficientMass_cleared_le_pow (arity P w) (terms P (pairFst w))
    (2 * BoundedCriticalFilters.gridDegree P (pairFst w)) (BoundedCriticalProjection.equationBits P (pairFst w))
    (BoundedCriticalRationalCoordinates.coordinateMass P (pairFst w))
    (sourceCoefficient P w) (FixedWidthPolynomial.entry (width P w))
    (BoundedCriticalFilters.numerator P (pairFst w)) (BoundedCriticalFilters.denominator P (pairFst w))
    ((family P).exponent_le w)
    (fun _ _ => (MvMass.coeff_le _ _).trans
      (BoundedCriticalProjection.equations_mass P (pairFst w) (BoundedCriticalFilters.row P w)))
    (fun i _ => (coordinate_bounds P (pairFst w) i).2.2.1)
    (fun i _ => (coordinate_bounds P (pairFst w) i).2.2.2)

end LeanCanny.Encoding.BoundedCriticalFilterBounds

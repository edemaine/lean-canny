/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionFamilyMacaulay
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace

/-! # Certified characteristic coefficients for arbitrary critical projection records -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionFamilyCharacteristic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionFamilyMacaulay
open BoundedProjectionMacaulay (dimension dimension_binary dimension_eq_pow)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (P : Readers) (record : List Bool → List Bool) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (AffineCharacteristic.subtractiveMatrix (matrix P record c)).det

theorem degree (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    (polynomial P record c).natDegree = dimension P c := by
  simpa only [polynomial, Fintype.card_fin] using
    AffineCharacteristic.subtractive_det_natDegree (matrix P record c)

theorem ne_zero (P : Readers) (record : List Bool → List Bool) (c : List Bool) : polynomial P record c ≠ 0 :=
  AffineCharacteristic.subtractive_det_ne_zero _

theorem coefficient_degree (P : Readers) (record : List Bool → List Bool) (c : List Bool) (v : ℕ) :
    ((polynomial P record c).coeff v).natDegree ≤ dimension P c := by
  simpa only [polynomial, Fintype.card_fin, Nat.mul_one] using
    CharacteristicLowestBounds.coefficient_degree_le (matrix P record c) 1 (matrix_degree P record c) v

theorem coefficient_bits (P : Readers) (record : List Bool → List Bool) (c : List Bool) (u v : ℕ) :
    (((polynomial P record c).coeff v).coeff u).natAbs.size ≤ BoundedCriticalProjection.coefficientBits P c := by
  have h := CharacteristicLowestBounds.all_coefficient_size_le (matrix P record c)
    (BoundedCriticalProjection.projectionBits P c) (matrix_mass P record c) v u
  simpa only [polynomial, Fintype.card_fin, dimension_eq_pow, BoundedCriticalProjection.coefficientBits] using h

noncomputable def reader {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : SpaceFunction record)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    CertifiedPolynomial.BivariateReader (polynomial P record) :=
  SubtractiveCharacteristicBits.reader (dimension P) (fun _ => 1) (matrix P record)
    (fun _ => by unfold dimension FixedWidthPolynomial.count; positivity)
    (dimension_binary h) (BinaryFn.const 1) (matrix_degree P record)
    (uniformEntry P record) (uniformEntry_evaluator h hr ha) (uniformEntry_packet P record)

theorem lowest_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    (polynomial P record c).trailingCoeff = BoundedProjectionFamily.polynomial P record c :=
  BoundedProjectionFamilyMacaulay.lowest_eq P record c

end LeanCanny.Encoding.BoundedProjectionFamilyCharacteristic

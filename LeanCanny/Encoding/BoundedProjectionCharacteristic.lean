/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionMacaulay
public import LeanCanny.Algebra.SubtractiveCharacteristicSpace

/-! # Certified characteristic coefficients for the selected projection system -/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionCharacteristic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionMacaulay
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (P : Readers) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (AffineCharacteristic.subtractiveMatrix (matrix P c)).det

theorem degree (P : Readers) (c : List Bool) :
    (polynomial P c).natDegree = dimension P c := by
  simpa only [polynomial, Fintype.card_fin] using
    AffineCharacteristic.subtractive_det_natDegree (matrix P c)

theorem ne_zero (P : Readers) (c : List Bool) : polynomial P c ≠ 0 :=
  AffineCharacteristic.subtractive_det_ne_zero _

theorem coefficient_degree (P : Readers) (c : List Bool) (v : ℕ) :
    ((polynomial P c).coeff v).natDegree ≤ dimension P c := by
  simpa only [polynomial, Fintype.card_fin, Nat.mul_one] using
    CharacteristicLowestBounds.coefficient_degree_le (matrix P c) 1 (matrix_degree P c) v

theorem coefficient_bits (P : Readers) (c : List Bool) (u v : ℕ) :
    (((polynomial P c).coeff v).coeff u).natAbs.size ≤ BoundedCriticalProjection.coefficientBits P c := by
  have h := CharacteristicLowestBounds.all_coefficient_size_le (matrix P c)
    (BoundedCriticalProjection.projectionBits P c) (matrix_mass P c) v u
  simpa only [polynomial, Fintype.card_fin, dimension_eq_pow, BoundedCriticalProjection.coefficientBits] using h

noncomputable def reader {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    CertifiedPolynomial.BivariateReader (polynomial P) :=
  SubtractiveCharacteristicBits.reader (dimension P) (fun _ => 1) (matrix P)
    (fun _ => by unfold dimension FixedWidthPolynomial.count; positivity)
    (dimension_binary h) (BinaryFn.const 1) (matrix_degree P)
    (uniformEntry P) (uniformEntry_evaluator h ha) (uniformEntry_packet P)

theorem lowest_eq (P : Readers) (c : List Bool) :
    (polynomial P c).trailingCoeff = BoundedCriticalProjection.polynomial P c :=
  BoundedProjectionMacaulay.lowest_eq P c

end LeanCanny.Encoding.BoundedProjectionCharacteristic

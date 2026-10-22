/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionRestriction

/-! # A uniform coefficient formula for projection-row terms

A term is an embedded source polynomial or partial derivative, optionally
multiplied by one direction variable. One direction-pattern guard, one source
coefficient, and one binary exponent factor suffice.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery
open LeanCanny.Encoding
open Geometry TubeEncoding TubeProjectionEncoding
open LeanCanny.Algebra
open scoped Classical

noncomputable def termPolynomial (n : ℕ) (p : MvPolynomial (Coordinate n) ℤ) (j : Coordinate n)
    (s : Option (Point n)) (derivative : Bool) : MvPolynomial (Variable n) ℤ :=
  MvPolynomial.rename ProjectionFlatten.coefficientEmbedding (if derivative then MvPolynomial.pderiv j p else p) *
    MvPolynomial.monomial (shiftVector n s) 1

theorem coeff_termPolynomial (n W : List Bool → ℕ) (target : List Bool → List Bool) (r : List Bool → Option ℕ)
    (c : List Bool) (p : MvPolynomial (Coordinate (n c)) ℤ) (j : Coordinate (n c))
    (s : Option (Point (n c))) (derivative : Bool) (hs : r c = s.map (fun i => (pointEquiv (n c) i).val)) :
    (termPolynomial (n c) p j s derivative).coeff (exponent n W target c) =
      if Pattern n W target r c then
        p.coeff (restriction n W target c + (if derivative then Finsupp.single j 1 else 0)) *
          ((if derivative then restriction n W target c j + 1 else 1 : ℕ) : ℤ)
      else 0 := by
  classical
  have h := EmbeddedCoefficient.coeff_rename_mul_monomial ProjectionFlatten.coefficientEmbedding
    ProjectionFlatten.coefficientEmbedding_injective (if derivative then MvPolynomial.pderiv j p else p)
    (exponent n W target c) (shiftVector (n c) s) (shiftVector_embedding (n c) s)
  change (termPolynomial (n c) p j s derivative).coeff (exponent n W target c) =
    if (restriction n W target c).mapDomain ProjectionFlatten.coefficientEmbedding + shiftVector (n c) s = exponent n W target c then
      (if derivative then MvPolynomial.pderiv j p else p).coeff (restriction n W target c) else 0 at h
  have he : (restriction n W target c).mapDomain ProjectionFlatten.coefficientEmbedding + shiftVector (n c) s = exponent n W target c ↔
      Pattern n W target r c := pattern_iff n W target r c s hs
  by_cases hp : Pattern n W target r c
  · rw [ite_eq_left (he.mpr hp)] at h
    rw [h, ite_eq_left hp]
    cases derivative <;> simp only [Bool.false_eq_true, ite_false, ite_true, add_zero, Nat.cast_one, mul_one, MvPolynomial.coeff_pderiv, Nat.cast_add]
  · rw [ite_eq_right (mt he.mp hp)] at h
    rw [h, ite_eq_right hp]

end LeanCanny.ETR.TubeProjectionQuery

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalPolynomialClearing
public import LeanCanny.Algebra.IntegerCoordinatePolynomials

/-! # Explicit bounded integer data for rational representations

One positive product of canonical coefficient denominators clears the eliminant
and every coordinate pair. A common degree cap D and rational component bit
bound B give an integer coefficient and scale budget
B*((2*n+1)*(D+1))+1. This is conditional on the rational source bounds; deriving
those bounds and coefficient access from multivariate input remains open.
-/

@[expose] public section

namespace LeanCanny.Algebra.BoundedIntegerCoordinates
open Polynomial IntegerCoordinatePolynomials

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] {p : τ → MvPolynomial ι ℚ}

def family (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p) : Option (Bool × ι) → ℚ[X]
  | none => r.polynomial
  | some (false, j) => r.numerator j
  | some (true, j) => r.denominator j

def integerData (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p)
    (D : ℕ) (hD : ∀ a, (family r a).natDegree ≤ D) : IntegerData r where
  polynomial := RationalPolynomialClearing.polynomial (family r) D none
  numerator := fun j => RationalPolynomialClearing.polynomial (family r) D (some (false, j))
  denominator := fun j => RationalPolynomialClearing.polynomial (family r) D (some (true, j))
  polynomial_scale := (RationalPolynomialClearing.scale (family r) D : ℤ)
  coordinate_scale := fun _ => (RationalPolynomialClearing.scale (family r) D : ℤ)
  polynomial_scale_ne_zero := Nat.cast_ne_zero.mpr (RationalPolynomialClearing.scale_pos _ _).ne'
  coordinate_scale_ne_zero := fun _ => Nat.cast_ne_zero.mpr (RationalPolynomialClearing.scale_pos _ _).ne'
  map_polynomial := by
    simpa only [Int.cast_natCast, family] using RationalPolynomialClearing.map_polynomial (family r) D hD none
  map_numerator := fun j => by
    simpa only [Int.cast_natCast, family] using
      RationalPolynomialClearing.map_polynomial (family r) D hD (some (false, j))
  map_denominator := fun j => by
    simpa only [Int.cast_natCast, family] using
      RationalPolynomialClearing.map_polynomial (family r) D hD (some (true, j))

omit [DecidableEq ι] in
def budget (D B : ℕ) : ℕ := B * ((2 * Fintype.card ι + 1) * (D + 1)) + 1

theorem family_coeff_size_le (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p)
    (D B : ℕ) (hB : ∀ a k, k ≤ D → ((family r a).coeff k).num.natAbs.size ≤ B ∧
      ((family r a).coeff k).den.size ≤ B) (a : Option (Bool × ι)) (k : ℕ) :
    ((RationalPolynomialClearing.polynomial (family r) D a).coeff k).natAbs.size ≤ budget (ι := ι) D B := by
  simpa only [budget, Fintype.card_option, Fintype.card_prod, Fintype.card_bool] using
    RationalPolynomialClearing.coeff_size_le (family r) D B hB a k

theorem coefficient_bounds (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p)
    (D : ℕ) (hD : ∀ a, (family r a).natDegree ≤ D) (B : ℕ)
    (hB : ∀ a k, k ≤ D → ((family r a).coeff k).num.natAbs.size ≤ B ∧ ((family r a).coeff k).den.size ≤ B) :
    (∀ k, (((integerData r D hD).polynomial).coeff k).natAbs.size ≤ budget (ι := ι) D B) ∧
      (∀ j k, (((integerData r D hD).numerator j).coeff k).natAbs.size ≤ budget (ι := ι) D B) ∧
      ∀ j k, (((integerData r D hD).denominator j).coeff k).natAbs.size ≤ budget (ι := ι) D B :=
  ⟨fun k => family_coeff_size_le r D B hB none k,
    fun j k => family_coeff_size_le r D B hB (some (false, j)) k,
    fun j k => family_coeff_size_le r D B hB (some (true, j)) k⟩

omit [DecidableEq ι] in
theorem scale_size_le (r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) p)
    (D B : ℕ) (hB : ∀ a k, k ≤ D → ((family r a).coeff k).den.size ≤ B) :
    (RationalPolynomialClearing.scale (family r) D).size ≤ budget (ι := ι) D B := by
  simpa only [budget, Fintype.card_option, Fintype.card_prod, Fintype.card_bool] using
    RationalPolynomialClearing.scale_size_le (family r) D B hB

end LeanCanny.Algebra.BoundedIntegerCoordinates

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalSpace

/-! # Rational composition with a chosen common clearing exponent

Any degree upper bound is sufficient for correctness. Choosing the exponent
from a source-derived bound keeps substitution linear in the outer integer
coefficients, avoiding recursive exact-degree scans during flattening.
-/

@[expose] public section

namespace LeanCanny.Algebra.UnivariateRational.Coordinate
open Polynomial

theorem compWith_actual (outer inner : Coordinate) : compWith outer.degree outer inner = outer.comp inner := rfl

end LeanCanny.Algebra.UnivariateRational.Coordinate

namespace LeanCanny.Algebra.UnivariateRational
open Polynomial

/-- The substitution operator is a matrix acting on the outer coefficient vector. -/
theorem clear_coeff (e : ℕ) (p n d : ℤ[X]) (j : ℕ) :
    (clear e p n d).coeff j = ∑ k ∈ Finset.range (e + 1), p.coeff k * (n ^ k * d ^ (e - k)).coeff j := by
  simp only [clear, mul_assoc, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]

end LeanCanny.Algebra.UnivariateRational

namespace LeanCanny.Algebra.RationalCoordinateBits
open LeanCanny.Computation LeanCanny.Algebra.UnivariateRational

theorem evaluatorsWithBound (outer inner : List Bool → Coordinate) (e : List Bool → ℕ) (he : LeanCanny.BinaryFn e)
    (ON : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).numerator)))
    (OD : SpaceFunction (PrimitivePairBits.coefficient (fun c => (outer c).denominator)))
    (IN : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).numerator)))
    (ID : SpaceFunction (PrimitivePairBits.coefficient (fun c => (inner c).denominator))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).compWith (e c) (inner c)).numerator)) ∧
    SpaceFunction (PrimitivePairBits.coefficient (fun c => ((outer c).compWith (e c) (inner c)).denominator)) :=
  ⟨UnivariateRationalBits.evaluator _ _ _ _ he ON IN ID, UnivariateRationalBits.evaluator _ _ _ _ he OD IN ID⟩

end LeanCanny.Algebra.RationalCoordinateBits

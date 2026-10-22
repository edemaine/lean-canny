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

noncomputable def compWith (e : ℕ) (outer inner : Coordinate) : Coordinate :=
  ⟨clear e outer.numerator inner.numerator inner.denominator,
   clear e outer.denominator inner.numerator inner.denominator⟩

theorem compWith_degree (e : ℕ) (outer inner : Coordinate) : (compWith e outer inner).degree ≤ e * inner.degree :=
  max_le (clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))
    (clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))

theorem eval_compWith {K : Type*} [Field K] (e : ℕ) (outer inner : Coordinate) (he : outer.degree ≤ e) (x : K)
    (hd : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0) :
    (compWith e outer inner).eval x = outer.eval (inner.eval x) := by
  have hn : outer.numerator.natDegree ≤ e := (le_max_left _ _).trans he
  have hden : outer.denominator.natDegree ≤ e := (le_max_right _ _).trans he
  simp only [eval, compWith]
  rw [eval₂_clear (Int.castRingHom K) e outer.numerator inner.numerator inner.denominator hn x hd,
    eval₂_clear (Int.castRingHom K) e outer.denominator inner.numerator inner.denominator hden x hd]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hd)

theorem compWith_denominator_ne_zero {K : Type*} [Field K] (e : ℕ) (outer inner : Coordinate)
    (he : outer.degree ≤ e) (x : K) (hi : inner.denominator.eval₂ (Int.castRingHom K) x ≠ 0)
    (ho : outer.denominator.eval₂ (Int.castRingHom K) (inner.eval x) ≠ 0) :
    (compWith e outer inner).denominator.eval₂ (Int.castRingHom K) x ≠ 0 := by
  change (clear _ _ _ _).eval₂ _ _ ≠ 0
  rw [eval₂_clear (Int.castRingHom K) e outer.denominator inner.numerator inner.denominator
    ((le_max_right _ _).trans he) x hi]
  exact mul_ne_zero (pow_ne_zero _ hi) ho

theorem compWith_mass (e : ℕ) (outer inner : Coordinate) (he : outer.degree ≤ e) (s b : ℕ)
    (hon : coefficientMass outer.numerator ≤ 2 ^ s) (hod : coefficientMass outer.denominator ≤ 2 ^ s)
    (hin : coefficientMass inner.numerator ≤ 2 ^ b) (hid : coefficientMass inner.denominator ≤ 2 ^ b) :
    coefficientMass (compWith e outer inner).numerator ≤ 2 ^ (s + e * b) ∧
    coefficientMass (compWith e outer inner).denominator ≤ 2 ^ (s + e * b) := by
  have hpow : 2 ^ s * (2 ^ b) ^ e = 2 ^ (s + e * b) := by rw [← pow_mul, ← pow_add, Nat.mul_comm b]
  exact ⟨(clear_mass _ _ _ _ ((le_max_left _ _).trans he) _ hin hid).trans ((Nat.mul_le_mul_right _ hon).trans_eq hpow),
    (clear_mass _ _ _ _ ((le_max_right _ _).trans he) _ hin hid).trans ((Nat.mul_le_mul_right _ hod).trans_eq hpow)⟩

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

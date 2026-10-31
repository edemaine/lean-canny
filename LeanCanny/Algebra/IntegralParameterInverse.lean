/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! # Constant denominators for nonzero integral parameter values

Strip the zero roots from an integer annihilator. Its remaining constant
coefficient is nonzero, and the negative shifted polynomial evaluates to
that constant divided by the parameter. A multiplication characteristic
polynomial supplies the annihilator even when the finite algebra is not
reduced or the parameter vanishes at some other algebraic branches.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralParameterInverse
open Polynomial
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]

noncomputable def tail (p : Polynomial R) : Polynomial R := p /ₘ (X ^ p.natTrailingDegree)

noncomputable def inverse (p : Polynomial R) : Polynomial R := -(tail p).divX

noncomputable def denominator (p : Polynomial R) : R := p.trailingCoeff

theorem factor (p : Polynomial R) : X ^ p.natTrailingDegree * tail p = p := by
  have hd : X ^ p.natTrailingDegree ∣ p :=
    X_pow_dvd_iff.mpr (fun _ hi => coeff_eq_zero_of_lt_natTrailingDegree hi)
  have H := modByMonic_add_div p (X ^ p.natTrailingDegree)
  rw [(modByMonic_eq_zero_iff_dvd (monic_X_pow _)).mpr hd, zero_add] at H
  exact H

theorem coeff_tail (p : Polynomial R) (k : ℕ) : (tail p).coeff k = p.coeff (k + p.natTrailingDegree) := by
  have H := congrArg (fun q : Polynomial R => q.coeff (k + p.natTrailingDegree)) (factor p)
  simpa only [coeff_X_pow_mul] using H

theorem tail_constant (p : Polynomial R) : (tail p).coeff 0 = denominator p := by
  simpa only [Nat.zero_add, denominator, trailingCoeff] using coeff_tail p 0

theorem coeff_inverse (p : Polynomial R) (k : ℕ) :
    (inverse p).coeff k = -p.coeff (k + 1 + p.natTrailingDegree) := by
  rw [inverse, coeff_neg, coeff_divX, coeff_tail]

theorem denominator_ne_zero (p : Polynomial R) (hp : p ≠ 0) : denominator p ≠ 0 :=
  trailingCoeff_nonzero_iff_nonzero.mpr hp

theorem natDegree_inverse_le (p : Polynomial R) : (inverse p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_inverse, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), neg_zero]

theorem inverse_coefficient_bound (p : Polynomial ℤ) (B : ℕ)
    (hp : ∀ k, (p.coeff k).natAbs ≤ B) (k : ℕ) : ((inverse p).coeff k).natAbs ≤ B := by
  simpa only [coeff_inverse, Int.natAbs_neg] using hp (k + 1 + p.natTrailingDegree)

theorem denominator_bound (p : Polynomial ℤ) (B : ℕ)
    (hp : ∀ k, (p.coeff k).natAbs ≤ B) : (denominator p).natAbs ≤ B :=
  hp p.natTrailingDegree

variable {K : Type*} [CommRing K] [IsDomain K]

theorem tail_root (p : Polynomial R) (φ : R →+* K) (x : K) (hx : x ≠ 0)
    (hp : p.eval₂ φ x = 0) : (tail p).eval₂ φ x = 0 := by
  have H := congrArg (fun q : Polynomial R => q.eval₂ φ x) (factor p)
  simp only [eval₂_mul, eval₂_pow, eval₂_X, hp] at H
  exact (mul_eq_zero.mp H).resolve_left (pow_ne_zero _ hx)

theorem mul_inverse_eval (p : Polynomial R) (φ : R →+* K) (x : K) (hx : x ≠ 0)
    (hp : p.eval₂ φ x = 0) : x * (inverse p).eval₂ φ x = φ (denominator p) := by
  have H := congrArg (fun q : Polynomial R => q.eval₂ φ x) (X_mul_divX_add (tail p))
  rw [eval₂_add, eval₂_mul, eval₂_X, eval₂_C, tail_root p φ x hx hp, tail_constant] at H
  rw [inverse, eval₂_neg]
  linear_combination -H

section Field
variable {L : Type*} [Field L]

theorem recover (p : Polynomial R) (φ : R →+* L) (x : L) (hx : x ≠ 0)
    (hp : p.eval₂ φ x = 0) (hc : φ (denominator p) ≠ 0) (t : L) :
    ((x * t) * (inverse p).eval₂ φ x) / φ (denominator p) = t := by
  have H := mul_inverse_eval p φ x hx hp
  calc
    _ = t * (x * (inverse p).eval₂ φ x) / φ (denominator p) := by ring
    _ = t := by rw [H]; exact mul_div_cancel_right₀ t hc

end Field

section Algebra
variable {A L ι : Type*} [CommRing A] [Field L]
    [Fintype ι] [DecidableEq ι]

theorem charpoly_root (b : Module.Basis ι ℤ A) (a : A) (φ : A →ₐ[ℤ] L) :
    (Algebra.leftMulMatrix b a).charpoly.eval₂ (Int.castRingHom L) (φ a) = 0 := by
  change Polynomial.aeval (φ a) (Algebra.leftMulMatrix b a).charpoly = 0
  rw [Polynomial.aeval_algHom_apply, Algebra.aeval_charpoly_leftMulMatrix, map_zero]

theorem charpoly_denominator_ne_zero (b : Module.Basis ι ℤ A) (a : A) :
    denominator (Algebra.leftMulMatrix b a).charpoly ≠ 0 :=
  denominator_ne_zero _ (Matrix.charpoly_monic _).ne_zero

variable [CharZero L]

theorem recover_algebra_value (b : Module.Basis ι ℤ A) (a : A) (φ : A →ₐ[ℤ] L)
    (ha : φ a ≠ 0) (t : L) :
    (((φ a) * t) * (inverse (Algebra.leftMulMatrix b a).charpoly).eval₂ (Int.castRingHom L) (φ a)) /
      ((denominator (Algebra.leftMulMatrix b a).charpoly : ℤ) : L) = t :=
  recover _ (Int.castRingHom L) (φ a) ha (charpoly_root b a φ)
    (Int.cast_ne_zero.mpr (charpoly_denominator_ne_zero b a)) t

end Algebra
end LeanCanny.Algebra.IntegralParameterInverse

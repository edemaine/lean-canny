/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UnivariateRationalCompositionWith
public import LeanCanny.Algebra.BalancedPrimitivePolynomials

/-! # Coordinate paths with fixed, source-derived clearing exponents

A path of k substitutions with stage degree at most D uses clearing exponent
D^j at stage j. Its degree is at most D^k; stage masses at most 2^b give
path masses at most 2^(k*D^k*b). These budgets have native binary writers.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalCoordinatePath
open Polynomial UnivariateRational

noncomputable def path (D : ℕ) (inner : ℕ → Coordinate) : ℕ → Coordinate
  | 0 => BalancedPrimitiveTree.identityCoordinate
  | k + 1 => (path D inner k).compWith (D ^ k) (inner k)

theorem degree_bound (D : ℕ) (inner : ℕ → Coordinate) (hi : ∀ k, (inner k).degree ≤ D) (k : ℕ) :
    (path D inner k).degree ≤ D ^ k := by
  cases k with
  | zero => norm_num [path, BalancedPrimitiveTree.identityCoordinate, Coordinate.degree]
  | succ k =>
    exact (Coordinate.compWith_degree _ _ _).trans ((Nat.mul_le_mul_left _ (hi k)).trans_eq (pow_succ D k).symm)

theorem mass_bound (D b : ℕ) (inner : ℕ → Coordinate) (hD : 1 ≤ D)
    (hi : ∀ k, (inner k).degree ≤ D)
    (hn : ∀ k, coefficientMass (inner k).numerator ≤ 2 ^ b)
    (hd : ∀ k, coefficientMass (inner k).denominator ≤ 2 ^ b) (k : ℕ) :
    coefficientMass (path D inner k).numerator ≤ 2 ^ (k * D ^ k * b) ∧
    coefficientMass (path D inner k).denominator ≤ 2 ^ (k * D ^ k * b) := by
  induction k with
  | zero =>
    have hx : coefficientMass (X : ℤ[X]) = 1 := by
      simpa only [Polynomial.monomial_one_one_eq_X, Int.natAbs_one] using coefficientMass_monomial 1 (1 : ℤ)
    have h1 : coefficientMass (1 : ℤ[X]) = 1 := by
      simpa only [← Polynomial.C_1, Int.natAbs_one] using coefficientMass_C (1 : ℤ)
    simp only [path, BalancedPrimitiveTree.identityCoordinate, hx, h1, zero_mul, pow_zero, le_refl, and_self]
  | succ k ih =>
    have H := Coordinate.compWith_mass (D ^ k) (path D inner k) (inner k) (degree_bound D inner hi k)
      (k * D ^ k * b) b ih.1 ih.2 (hn k) (hd k)
    have he : k * D ^ k * b + D ^ k * b ≤ (k + 1) * D ^ (k + 1) * b := by
      calc
        _ = (k + 1) * D ^ k * b := by ring
        _ ≤ _ := Nat.mul_le_mul_right b (Nat.mul_le_mul_left (k + 1) (Nat.pow_le_pow_right hD (by omega)))
    exact ⟨H.1.trans (Nat.pow_le_pow_right (by decide) he), H.2.trans (Nat.pow_le_pow_right (by decide) he)⟩

noncomputable def evalPath {K : Type*} [Field K] (inner : ℕ → Coordinate) : ℕ → K → K
  | 0, x => x
  | k + 1, x => evalPath inner k ((inner k).eval x)

def Defined {K : Type*} [Field K] (inner : ℕ → Coordinate) : ℕ → K → Prop
  | 0, _ => True
  | k + 1, x => (inner k).denominator.eval₂ (Int.castRingHom K) x ≠ 0 ∧ Defined inner k ((inner k).eval x)

theorem path_spec {K : Type*} [Field K] (D : ℕ) (inner : ℕ → Coordinate)
    (hi : ∀ k, (inner k).degree ≤ D) (k : ℕ) (x : K) (hx : Defined inner k x) :
    (path D inner k).denominator.eval₂ (Int.castRingHom K) x ≠ 0 ∧ (path D inner k).eval x = evalPath inner k x := by
  induction k generalizing x with
  | zero => simp only [path, BalancedPrimitiveTree.identityCoordinate, Polynomial.eval₂_one, one_ne_zero,
      ne_eq, not_false_eq_true, Coordinate.eval, Polynomial.eval₂_X, div_one, evalPath, and_self]
  | succ k ih =>
    obtain ⟨hd, hx'⟩ := hx
    obtain ⟨hden, he⟩ := ih _ hx'
    exact ⟨Coordinate.compWith_denominator_ne_zero _ _ _ (degree_bound D inner hi k) _ hd hden,
      (Coordinate.eval_compWith _ _ _ (degree_bound D inner hi k) _ hd).trans he⟩

theorem degreeBudget_binary {D k : List Bool → ℕ} (hD : LeanCanny.BinaryFn D) (hk : LeanCanny.UnaryFn k) :
    LeanCanny.BinaryFn (fun c => D c ^ k c) := hD.powUnary hk

theorem massBudget_binary {D b k : List Bool → ℕ} (hD : LeanCanny.BinaryFn D) (hb : LeanCanny.BinaryFn b) (hk : LeanCanny.UnaryFn k) :
    LeanCanny.BinaryFn (fun c => k c * D c ^ k c * b c) :=
  ((LeanCanny.BinaryFn.of_bits (LeanCanny.bits_mem_FP hk)).mul (hD.powUnary hk)).mul hb

end LeanCanny.Algebra.RationalCoordinatePath

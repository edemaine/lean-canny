/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedPrimitiveCoordinates
public import LeanCanny.Algebra.SeparableIntegerCoordinates

/-! # Integer numerator and denominator polynomials for balanced leaf recovery

Each branch composes two polynomial ratios with one common clearing exponent.
The resulting denominator is nonzero at every parameter root, and the ratio
agrees with the nested decoder over every characteristic-zero field.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedPrimitiveTree
open Polynomial
open UnivariateRational

noncomputable def identityCoordinate : Coordinate := ⟨X, 1⟩

noncomputable def flat (a : ℕ → SeparableIntegerPolynomial) : ℕ → ℕ → ℕ → Coordinate
  | 0, _, _ => identityCoordinate
  | h + 1, i, j =>
    if j < 2 ^ h then (flat a h (2 * i) j).comp ((node a h (2 * i)).leftCoordinate (node a h (2 * i + 1)))
    else (flat a h (2 * i + 1) (j - 2 ^ h)).comp ((node a h (2 * i)).rightCoordinate (node a h (2 * i + 1)))

theorem flat_spec {K : Type*} [Field K] [CharZero K] (a : ℕ → SeparableIntegerPolynomial)
    (h i j : ℕ) (theta : K) (ht : (node a h i).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    (flat a h i j).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
      (flat a h i j).eval theta = coordinate h (decode a h i theta) j := by
  induction h generalizing i j theta with
  | zero => simp only [flat, identityCoordinate, Polynomial.eval₂_one, ne_eq, one_ne_zero, not_false_eq_true,
      Coordinate.eval, Polynomial.eval₂_X, div_one, coordinate, decode, and_self]
  | succ h ih =>
    have hr := SeparableIntegerPolynomial.decode_root_over (node a h (2 * i)) (node a h (2 * i + 1)) theta ht
    have hd := SeparableIntegerPolynomial.denominator_ne_zero_over (node a h (2 * i)) (node a h (2 * i + 1)) theta ht
    by_cases hj : j < 2 ^ h
    · have hl := ih (2 * i) j _ hr.1
      simp only [flat, ite_eq_left hj]
      refine ⟨Coordinate.comp_denominator_ne_zero _ _ theta hd hl.1, ?_⟩
      have he := (Coordinate.eval_comp (flat a h (2 * i) j)
        ((node a h (2 * i)).leftCoordinate (node a h (2 * i + 1))) theta hd).trans hl.2
      simpa only [coordinate, decode, ite_eq_left hj] using he
    · have hh := ih (2 * i + 1) (j - 2 ^ h) _ hr.2.1
      simp only [flat, ite_eq_right hj]
      refine ⟨Coordinate.comp_denominator_ne_zero _ _ theta hd hh.1, ?_⟩
      have he := (Coordinate.eval_comp (flat a h (2 * i + 1) (j - 2 ^ h))
        ((node a h (2 * i)).rightCoordinate (node a h (2 * i + 1))) theta hd).trans hh.2
      simpa only [coordinate, decode, ite_eq_right hj] using he

noncomputable def degreeBudget (a : ℕ → SeparableIntegerPolynomial) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, i => max (degreeBudget a h (2 * i)) (degreeBudget a h (2 * i + 1)) *
      ((node a h (2 * i)).polynomial.natDegree * (node a h (2 * i + 1)).polynomial.natDegree + 2)

theorem flat_degree (a : ℕ → SeparableIntegerPolynomial) (h i j : ℕ) :
    (flat a h i j).degree ≤ degreeBudget a h i := by
  induction h generalizing i j with
  | zero => norm_num [flat, identityCoordinate, Coordinate.degree, degreeBudget]
  | succ h ih =>
    by_cases hj : j < 2 ^ h
    · rw [flat, ite_eq_left hj]
      exact (Coordinate.comp_degree _ _).trans (Nat.mul_le_mul
        ((ih _ _).trans (le_max_left _ _)) (SeparableIntegerPolynomial.leftCoordinate_degree _ _))
    · rw [flat, ite_eq_right hj]
      exact (Coordinate.comp_degree _ _).trans (Nat.mul_le_mul
        ((ih _ _).trans (le_max_right _ _)) (SeparableIntegerPolynomial.rightCoordinate_degree _ _))

private theorem pow_add_two (D t : ℕ) (ht : 0 < t) : D ^ t + 2 ≤ (D + 2) ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases hz : t = 0
    · subst t; simp
    · calc
        D ^ (t + 1) + 2 ≤ (D ^ t + 2) * (D + 2) := by
          rw [pow_succ]
          calc
            D ^ t * D + 2 ≤ D ^ t * D + (2 * D ^ t + 2 * D + 4) := by omega
            _ = _ := by ring
        _ ≤ (D + 2) ^ t * (D + 2) := Nat.mul_le_mul_right _ (ih (by omega))
        _ = _ := (pow_succ _ _).symm

theorem degreeBudget_le (a : ℕ → SeparableIntegerPolynomial) (D : ℕ)
    (ha : ∀ i, (a i).polynomial.natDegree ≤ D) (h i : ℕ) :
    degreeBudget a h i ≤ (D + 2) ^ (2 ^ (h + 1)) := by
  induction h generalizing i with
  | zero => exact Nat.one_le_pow _ _ (by omega)
  | succ h ih =>
    have hl := degree_le_pow a h (2 * i) D (fun j _ => ha _)
    have hr := degree_le_pow a h (2 * i + 1) D (fun j _ => ha _)
    have hp : (node a h (2 * i)).polynomial.natDegree * (node a h (2 * i + 1)).polynomial.natDegree ≤ D ^ (2 ^ (h + 1)) := by
      apply (Nat.mul_le_mul hl hr).trans_eq
      rw [← pow_add, pow_succ]
      congr 1
      omega
    have hf := (Nat.add_le_add_right hp 2).trans (pow_add_two D (2 ^ (h + 1)) (by positivity))
    apply (Nat.mul_le_mul (max_le (ih _) (ih _)) hf).trans_eq
    rw [← pow_add, pow_succ (2 : ℕ) (h + 1)]
    congr 1
    omega

end LeanCanny.Algebra.BalancedPrimitiveTree

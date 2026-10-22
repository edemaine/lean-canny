/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedTree
public import LeanCanny.Algebra.UnivariateRationalComposition

/-! # Actual bivariate rational coordinates for symbolic tree leaves -/

@[expose] public section

namespace LeanCanny.Algebra.SymbolicBalancedCoordinate
open Polynomial SymbolicScaledSquarefree SymbolicPrimitivePair
open scoped Classical BigOperators

structure Coordinate where
  numerator : Polynomial Coefficient
  denominator : Polynomial Coefficient

namespace Coordinate

noncomputable def degree (r : Coordinate) : ℕ := max r.numerator.natDegree r.denominator.natDegree

noncomputable def eval {L : Type*} [Field L] (r : Coordinate) (φ : Coefficient →+* L) (x : L) : L :=
  r.numerator.eval₂ φ x / r.denominator.eval₂ φ x

noncomputable def comp (outer inner : Coordinate) : Coordinate :=
  ⟨UnivariateRational.clear outer.degree outer.numerator inner.numerator inner.denominator,
    UnivariateRational.clear outer.degree outer.denominator inner.numerator inner.denominator⟩

theorem comp_degree (outer inner : Coordinate) : (comp outer inner).degree ≤ outer.degree * inner.degree :=
  max_le (UnivariateRational.clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))
    (UnivariateRational.clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))

theorem eval_comp {L : Type*} [Field L] (outer inner : Coordinate) (φ : Coefficient →+* L) (x : L)
    (hd : inner.denominator.eval₂ φ x ≠ 0) :
    (comp outer inner).eval φ x = outer.eval φ (inner.eval φ x) := by
  simp only [eval, comp]
  rw [UnivariateRational.eval₂_clear φ outer.degree outer.numerator inner.numerator inner.denominator (le_max_left _ _) x hd,
    UnivariateRational.eval₂_clear φ outer.degree outer.denominator inner.numerator inner.denominator (le_max_right _ _) x hd]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hd)

theorem comp_denominator_ne_zero {L : Type*} [Field L] (outer inner : Coordinate) (φ : Coefficient →+* L) (x : L)
    (hi : inner.denominator.eval₂ φ x ≠ 0)
    (ho : outer.denominator.eval₂ φ (inner.eval φ x) ≠ 0) :
    (comp outer inner).denominator.eval₂ φ x ≠ 0 := by
  change (UnivariateRational.clear _ _ _ _).eval₂ φ x ≠ 0
  rw [UnivariateRational.eval₂_clear φ outer.degree outer.denominator inner.numerator inner.denominator (le_max_right _ _) x hi]
  exact mul_ne_zero (pow_ne_zero _ hi) ho

end Coordinate

noncomputable def identity : Coordinate := ⟨X, 1⟩

noncomputable def pair (right : Bool) (p q : SeparablePolynomial) : Coordinate :=
  ⟨if right then rightNumerator p q else leftNumerator p q, denominator p q⟩

theorem eval_pair_false {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : SeparablePolynomial) (theta : L) :
    (pair false p q).eval φ theta = (evaluatedCoordinates φ p q theta).1 := rfl

theorem eval_pair_true {L : Type*} [Field L] (φ : Coefficient →+* L)
    (p q : SeparablePolynomial) (theta : L) :
    (pair true p q).eval φ theta = (evaluatedCoordinates φ p q theta).2 := rfl

noncomputable def coordinate (a : ℕ → SeparablePolynomial) : ℕ → ℕ → ℕ → Coordinate
  | 0, _, _ => identity
  | h + 1, i, j =>
    if j < 2 ^ h then
      (coordinate a h (2 * i) j).comp
        (pair false (SymbolicBalancedTree.node a h (2 * i)) (SymbolicBalancedTree.node a h (2 * i + 1)))
    else (coordinate a h (2 * i + 1) (j - 2 ^ h)).comp
      (pair true (SymbolicBalancedTree.node a h (2 * i)) (SymbolicBalancedTree.node a h (2 * i + 1)))

theorem coordinate_spec (a : ℕ → SeparablePolynomial) (b : ℕ → ℕ)
    (hm : ∀ i k, coefficientMass ((a i).polynomial.coeff k) ≤ 2 ^ b i)
    (beta : ℝ) (hb : 0 < beta) (h i j : ℕ) (hj : j < 2 ^ h)
    (he : beta ≤ InfinitesimalSign.dyadic (SymbolicBalancedTree.exponent a b h i)) (theta : ℝ)
    (ht : (SymbolicBalancedTree.node a h i).polynomial.eval₂ (scalarEvaluation beta) theta = 0) :
    (coordinate a h i j).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 ∧
      (coordinate a h i j).eval (scalarEvaluation beta) theta =
        BalancedPrimitiveTree.coordinate h (SymbolicBalancedTree.decode a beta h i theta) j := by
  induction h generalizing i j theta with
  | zero => simp only [coordinate, identity, Polynomial.eval₂_one, one_ne_zero,
      ne_eq, not_false_eq_true, Coordinate.eval, Polynomial.eval₂_X, div_one,
      SymbolicBalancedTree.decode, BalancedPrimitiveTree.coordinate, and_self]
  | succ h ih =>
    have hel : beta ≤ InfinitesimalSign.dyadic (SymbolicBalancedTree.exponent a b h (2 * i)) :=
      he.trans (dyadic_antitone (by rw [SymbolicBalancedTree.exponent]; omega))
    have her : beta ≤ InfinitesimalSign.dyadic (SymbolicBalancedTree.exponent a b h (2 * i + 1)) :=
      he.trans (dyadic_antitone (by rw [SymbolicBalancedTree.exponent]; omega))
    have hep : beta ≤ InfinitesimalSign.dyadic (smallExponent
        (SymbolicBalancedTree.node a h (2 * i)) (SymbolicBalancedTree.node a h (2 * i + 1))
        (SymbolicBalancedTree.massBudget a b h (2 * i)) (SymbolicBalancedTree.massBudget a b h (2 * i + 1))) :=
      he.trans (dyadic_antitone (by rw [SymbolicBalancedTree.exponent]; omega))
    have hr := small_decode_root _ _ _ _
      (SymbolicBalancedTree.coefficient_mass a b hm h (2 * i))
      (SymbolicBalancedTree.coefficient_mass a b hm h (2 * i + 1)) beta hb hep theta ht
    by_cases hjl : j < 2 ^ h
    · have hc := ih (2 * i) j hjl hel _ hr.1
      have hd : (pair false (SymbolicBalancedTree.node a h (2 * i))
          (SymbolicBalancedTree.node a h (2 * i + 1))).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 := hr.2.2.2
      refine ⟨?_, ?_⟩
      · rw [coordinate, ite_eq_left hjl]
        exact Coordinate.comp_denominator_ne_zero _ _ _ _ hd hc.1
      · rw [coordinate, ite_eq_left hjl, Coordinate.eval_comp _ _ _ _ hd]
        simpa only [SymbolicBalancedTree.decode, BalancedPrimitiveTree.coordinate, ite_eq_left hjl,
          eval_pair_false] using hc.2
    · have hjr : j - 2 ^ h < 2 ^ h := by rw [pow_succ] at hj; omega
      have hc := ih (2 * i + 1) (j - 2 ^ h) hjr her _ hr.2.1
      have hd : (pair true (SymbolicBalancedTree.node a h (2 * i))
          (SymbolicBalancedTree.node a h (2 * i + 1))).denominator.eval₂ (scalarEvaluation beta) theta ≠ 0 := hr.2.2.2
      refine ⟨?_, ?_⟩
      · rw [coordinate, ite_eq_right hjl]
        exact Coordinate.comp_denominator_ne_zero _ _ _ _ hd hc.1
      · rw [coordinate, ite_eq_right hjl, Coordinate.eval_comp _ _ _ _ hd]
        simpa only [SymbolicBalancedTree.decode, BalancedPrimitiveTree.coordinate, ite_eq_right hjl,
          eval_pair_true] using hc.2

end LeanCanny.Algebra.SymbolicBalancedCoordinate

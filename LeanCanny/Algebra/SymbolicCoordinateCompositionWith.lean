/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicBalancedCoordinates

/-! # Symbolic coordinates with explicit clearing exponents -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicBalancedCoordinate
open Polynomial SymbolicScaledSquarefree
namespace Coordinate

noncomputable def compWith (e : ℕ) (outer inner : Coordinate) : Coordinate :=
  ⟨UnivariateRational.clear e outer.numerator inner.numerator inner.denominator,
    UnivariateRational.clear e outer.denominator inner.numerator inner.denominator⟩

lemma compWith_degree (e : ℕ) (outer inner : Coordinate) :
    (compWith e outer inner).degree ≤ e * inner.degree :=
  max_le (UnivariateRational.clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))
    (UnivariateRational.clear_degree _ _ _ _ _ (le_max_left _ _) (le_max_right _ _))

lemma eval_compWith {L : Type*} [Field L] (e : ℕ) (outer inner : Coordinate)
    (he : outer.degree ≤ e) (φ : Coefficient →+* L) (x : L)
    (hd : inner.denominator.eval₂ φ x ≠ 0) :
    (compWith e outer inner).eval φ x = outer.eval φ (inner.eval φ x) := by
  simp only [eval, compWith]
  rw [UnivariateRational.eval₂_clear φ e outer.numerator inner.numerator inner.denominator
      ((le_max_left _ _).trans he) x hd,
    UnivariateRational.eval₂_clear φ e outer.denominator inner.numerator inner.denominator
      ((le_max_right _ _).trans he) x hd]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hd)

lemma compWith_denominator_ne_zero {L : Type*} [Field L] (e : ℕ) (outer inner : Coordinate)
    (he : outer.degree ≤ e) (φ : Coefficient →+* L) (x : L)
    (hi : inner.denominator.eval₂ φ x ≠ 0)
    (ho : outer.denominator.eval₂ φ (inner.eval φ x) ≠ 0) :
    (compWith e outer inner).denominator.eval₂ φ x ≠ 0 := by
  change (UnivariateRational.clear _ _ _ _).eval₂ φ x ≠ 0
  rw [UnivariateRational.eval₂_clear φ e outer.denominator inner.numerator inner.denominator
    ((le_max_right _ _).trans he) x hi]
  exact mul_ne_zero (pow_ne_zero _ hi) ho

end Coordinate
end LeanCanny.Algebra.SymbolicBalancedCoordinate

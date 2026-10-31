/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionCoefficientMap
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Entry heights of actual pure-power reductions

Reduction entries only select the common leading coefficient, select and
negate one lower coefficient, or return zero. An additive integer extraction
therefore preserves a common entry bound without a degree or rank factor.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralReductionHeightBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {n B M : ℕ}

theorem matrix_height (f : A →+ ℤ) (fallback : Fin n) (d : Fin n → ℕ)
    (low : Fin n → MvPolynomial (Fin n) A) (c : A) (bound H : ℕ)
    (hlow : ∀ i e, (f ((low i).coeff e)).natAbs ≤ 2 ^ H) (hc : (f c).natAbs ≤ 2 ^ H)
    (i j : PurePowerReductionMatrix.Index n B) :
    (f (PurePowerReductionMatrix.matrix fallback d low c bound i j)).natAbs ≤ 2 ^ H := by
  unfold PurePowerReductionMatrix.matrix
  by_cases hn : PurePowerReductionMatrix.Normal d (FixedWidthPolynomial.vector n B j)
  · rw [ite_eq_left hn]
    by_cases hij : i = j
    · rw [ite_eq_left hij]
      exact hc
    · rw [ite_eq_right hij, map_zero, Int.natAbs_zero]
      exact Nat.zero_le _
  · rw [ite_eq_right hn]
    by_cases hv : (FixedWidthPolynomial.vector n B j).degree ≤ bound
    · rw [ite_eq_left hv, MonicMonomialReduction.step_coefficient]
      split_ifs
      · rw [map_neg, Int.natAbs_neg]
        exact hlow _ _
      · rw [map_zero, Int.natAbs_zero]
        exact Nat.zero_le _
    · rw [ite_eq_right hv, map_zero, Int.natAbs_zero]
      exact Nat.zero_le _

theorem integer_entry_height (b : Module.Basis (Fin M) ℤ A) (z : ℤ) (G : ℕ) (h : z.natAbs ≤ 2 ^ G) (r t : Fin M) :
    (Algebra.leftMulMatrix b (z : A) r t).natAbs ≤ 2 ^ G := by
  rw [map_intCast, Matrix.intCast_apply]
  split_ifs
  · simpa only [Int.cast_id] using h
  · rw [Int.cast_zero, Int.natAbs_zero]
    exact Nat.zero_le _

end LeanCanny.Algebra.IntegralReductionHeightBounds

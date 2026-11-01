/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCriticalRoot
/-! # The formal relative critical degree is bounded before specialization -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCriticalRoot
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem degree_le {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hm : m ≤ S) (r : CriticalRule n) :
    (criticalPolynomial x hm r).natDegree ≤ criticalDegree x hm r := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [equation]
  unfold CoordinateFrozenCriticalElimination.polynomial ClearedCoordinateCritical.annihilator PurePowerRelativeAnnihilator.polynomial
  rw [ScaledGradedReductionAnnihilator.coefficient, Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact hk

end LeanCanny.Algebra.IntegralMixedCriticalRoot

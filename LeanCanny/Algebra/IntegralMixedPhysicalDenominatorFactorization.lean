/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalDenominatorValue
/-! # Physical spatial clearing uses the actual bank product and original scales -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedHistory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem factorization (F : Family) (q : List Bool) :
    IntegralMixedPhysicalCriticalBits.denominator F q =
      commonDenominator (F.state q) ^ (F.ambient q + 1) * ∏ i, (F.rule q).scales i := by
  unfold IntegralMixedPhysicalCriticalBits.denominator CoordinateFrozenCriticalElimination.denominator
    CommonIntegerDenominator.denominator
  change (∏ i : Fin (F.ambient q + 1), commonDenominator (F.state q) * (F.rule q).scales i) = _
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end LeanCanny.Algebra.IntegralMixedPhysicalDenominatorBits

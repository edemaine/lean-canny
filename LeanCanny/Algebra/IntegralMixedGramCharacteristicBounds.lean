/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramCharacteristicSource

/-! # Actual Gram characteristic blocks fit the one original-source cap -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramCharacteristicBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedGramCharacteristicSource
open scoped Classical

theorem scalar_rank_le (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) :
    2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ≤ rankCap P (RankedHistoryTask.root q) := by
  rw [g.width]
  change 2 ^ P.width _ ≤ (2 ^ P.width _) ^ (P.cap _ + 1)
  conv_lhs => rw [← pow_one (2 ^ P.width (RankedHistoryTask.root q))]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)

theorem dimension_succ_le (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) :
    (source P F).dimension q + 1 ≤ rankCap P (RankedHistoryTask.root q) :=
  (Nat.succ_le_of_lt (IntegralMixedValueTaskBounds.columns_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q)).trans
    (scalar_rank_le P F g q)

theorem rank_le (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    (source P F).rank q ≤ rankCap P (RankedHistoryTask.root q) := auxiliary_rank_le P F g q hv 2 (by decide)

theorem power_cap (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    IntegralBerkowitzBlockBits.powerDimension (source P F) q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HD := dimension_succ_le P F g q
  have HR := rank_le P F g q hv
  have HH : IntegralBerkowitzBlockBits.powerDimension (source P F) q ≤ (rankCap P (RankedHistoryTask.root q)) ^ 3 := by
    change (((source P F).dimension q + 1) * ((source P F).dimension q + 1)) * (source P F).rank q ≤ _
    calc
      _ ≤ (rankCap P (RankedHistoryTask.root q) * rankCap P (RankedHistoryTask.root q)) * rankCap P (RankedHistoryTask.root q) :=
        Nat.mul_le_mul (Nat.mul_le_mul HD HD) HR
      _ = _ := by ring
  apply HH.trans
  apply le_trans _ (IntegralCriticalQueryBounds.retained_grid_le _ _ _ _ _ _ _ _)
  apply Nat.pow_le_pow_right
  · exact Nat.pow_pos (Nat.two_pow_pos _)
  · omega

theorem action_cap (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    (source P F).dimension q * (source P F).rank q ≤ numericCap P (RankedHistoryTask.root q) := by
  apply le_trans _ (power_cap P F g q hv)
  change _ ≤ (((source P F).dimension q + 1) * ((source P F).dimension q + 1)) * (source P F).rank q
  apply Nat.mul_le_mul_right
  exact (Nat.le_succ _).trans (Nat.le_mul_self _)

end LeanCanny.Algebra.IntegralMixedGramCharacteristicBounds

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicSource
/-! # PSC characteristic arithmetic fits the one original-source cap -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps IntegralMixedExceptionalBounds
open scoped Classical

theorem twice_coordinate_le_auxiliary {n : ℕ} (T : IntegralMixedHistory.SpatialSource n)
    (r : IntegralMixedCriticalSweep.Rule n) :
    2 * IntegralMixedCoordinateSquarefree.coordinateDegree T r ≤ auxiliaryCap (n + 1) T.degree := by
  have HK := coordinateCap_le T.degree r
  have HD : 0 < T.degree := by have H := T.degree_two; omega
  have HF : 1 ≤ (PurePowerReductionBounds.bound (n + 1) T.degree + 1) * T.degree :=
    Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) HD)
  have HE : K (n + 1) T.degree ≤ E (n + 1) T.degree := by
    change PurePowerReductionBounds.dimension (n + 1) T.degree ≤
      PurePowerReductionBounds.dimension (n + 1) T.degree *
        ((PurePowerReductionBounds.bound (n + 1) T.degree + 1) * T.degree)
    exact (Nat.mul_one _).symm.trans_le (Nat.mul_le_mul_left _ HF)
  unfold auxiliaryCap IntegralMixedCoordinateSquarefree.coordinateDegree
  omega

theorem dimension_succ_scalar (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).dimension q + 1 ≤ 2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) := by
  have HD := IntegralMixedPscEntryBits.degree_pos P F q
  have HN : (source P F).dimension q + 1 ≤ 2 * IntegralMixedPscEntryBits.degree P F q := by
    change (IntegralMixedPscEntryBits.degree P F q - (IntegralMixedPscEntryBits.index P F q).val) +
      (IntegralMixedPscEntryBits.degree P F q - 1 - (IntegralMixedPscEntryBits.index P F q).val) + 1 ≤ _
    omega
  exact HN.trans ((twice_coordinate_le_auxiliary
    (F.spatial (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q))).trans
      (F.scalar_cap (IntegralMixedVirtualTaskBits.saved P q)))

theorem scalar_rank_le (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) :
    2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q) ≤ rankCap P (RankedHistoryTask.root q) := by
  rw [g.width]
  change 2 ^ P.width _ ≤ (2 ^ P.width _) ^ (P.cap _ + 1)
  conv_lhs => rw [← pow_one (2 ^ P.width (RankedHistoryTask.root q))]
  exact Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)

theorem rank_le (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    (source P F).rank q ≤ rankCap P (RankedHistoryTask.root q) := auxiliary_rank_le P F g q hv 1 (by decide)

theorem power_cap (P : Parameters) (F : Family) (g : RootGeometry P F) (q : List Bool) (hv : valid P q) :
    IntegralBerkowitzBlockBits.powerDimension (source P F) q ≤ numericCap P (RankedHistoryTask.root q) := by
  have HD := (dimension_succ_scalar P F q).trans (scalar_rank_le P F g q)
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

end LeanCanny.Algebra.IntegralMixedPscCharacteristicBits

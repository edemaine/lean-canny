/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationTopSource
public import LeanCanny.Algebra.IntegralBerkowitzBlockEntry
/-! # Normalization block indices fit the existing native root cap

The integer characteristic source has dimension equal to the old algebra
rank and coefficient rank one. The retained-grid term in the existing cap
also covers its quadratic relative coefficient matrix.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

theorem dimension_rankCap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    dimension F (IntegralMixedVirtualTaskBits.saved P q) ≤ rankCap P (RankedHistoryTask.root q) :=
  IntegralMixedVirtualCaps.auxiliary_rank_le P F g q hv 0 (by decide)

theorem factor_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    powerDimension (source P F) q ≤ numericCap P (RankedHistoryTask.root q) := by
  let r := RankedHistoryTask.root q
  let R := rankCap P r
  let L := PurePowerReductionBounds.dimension (P.ambient r + 1) (P.degree r)
  let d := dimension F (IntegralMixedVirtualTaskBits.saved P q)
  have HD : d ≤ R := dimension_rankCap P F g q hv
  have HR : 0 < R := pow_pos (Nat.two_pow_pos _) _
  have HL : 0 < L := pow_pos (Nat.two_pow_pos _) _
  change ((d + 1) * (d + 1)) * 1 ≤ _
  rw [Nat.mul_one]
  by_cases H2 : 2 ≤ R
  · have HA : R + 1 ≤ R ^ 2 := by
      calc R + 1 ≤ 2 * R := by omega
           _ ≤ R * R := Nat.mul_le_mul_right R H2
           _ = R ^ 2 := by ring
    have HB : (d + 1) * (d + 1) ≤ R ^ 4 := by
      calc
        _ ≤ (R + 1) * (R + 1) := Nat.mul_le_mul (Nat.add_le_add_right HD 1) (Nat.add_le_add_right HD 1)
        _ ≤ (R ^ 2) * (R ^ 2) := Nat.mul_le_mul HA HA
        _ = R ^ 4 := by ring
    have HC : R ^ 4 ≤ R ^ ((P.ambient r + 1) + 3) := Nat.pow_le_pow_right HR (by omega)
    have HE : R ^ ((P.ambient r + 1) + 3) ≤ numericCap P r := by
      unfold numericCap
      exact IntegralCriticalQueryBounds.retained_grid_le _ _ _ _ _ _ _ _
    exact HB.trans (HC.trans HE)
  · have HE : R = 1 := by omega
    have HD1 : d ≤ 1 := by omega
    have HA : (d + 1) * (d + 1) ≤ 4 := by nlinarith
    have HB : 4 ≤ IntegralCoefficientBlocks.dimension L R := by
      rw [HE]
      unfold IntegralCoefficientBlocks.dimension
      nlinarith
    have HC : IntegralCoefficientBlocks.dimension L R ≤ numericCap P r := by
      unfold numericCap
      exact IntegralCriticalQueryBounds.coefficient_block_le _ _ _ _ _ _ _ _
    exact HA.trans (HB.trans HC)

theorem augmented_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) :
    ((source P F).dimension q + 2) * (source P F).rank q ≤ numericCap P (RankedHistoryTask.root q) := by
  let r := RankedHistoryTask.root q
  let R := rankCap P r
  have HD : dimension F (IntegralMixedVirtualTaskBits.saved P q) ≤ R := dimension_rankCap P F g q hv
  have HR : 0 < R := pow_pos (Nat.two_pow_pos _) _
  change (dimension F (IntegralMixedVirtualTaskBits.saved P q) + 2) * 1 ≤ _
  rw [Nat.mul_one]
  have HA : dimension F (IntegralMixedVirtualTaskBits.saved P q) + 2 ≤ 3 * R := by omega
  have HB : 3 * R ≤ ((P.ambient r + 1) + 3) * R := Nat.mul_le_mul_right R (by omega)
  have HC : ((P.ambient r + 1) + 3) * R ≤ numericCap P r := by
    unfold numericCap
    exact IntegralCriticalQueryBounds.product_block_le _ _ _ _ _ _ _ _
  exact HA.trans (HB.trans HC)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

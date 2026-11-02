/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitHeightProfile
public import LeanCanny.Algebra.IntegralMixedFullHeightControls
/-! # Legacy full-history ceilings are dominated by the limit profile

This comparison is separate from the new core profile, so FullScriptHeight
can import that profile without a dependency cycle.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitHeightProfile
open LeanCanny.Encoding FixedWidthPolynomial UniformIntegralPrefix

theorem legacy_cutFactor_le (n S B W D L : ℕ) : IntegralMixedFullScriptHeight.cutFactor n S B W D L ≤ cutFactor n S B W D L :=
  IntegralMixedHeightScaling.normalized_mono (Nat.le_refl _) (legacy_factor_le _ _ _ _ _ _)

theorem legacy_coefficientFactor_le (n S B W D L : ℕ) :
    IntegralMixedFullScriptHeight.coefficientFactor n S B W D L ≤ coefficientFactor n S B W D L :=
  Nat.add_le_add_right (max_le_max (Nat.le_refl _) (legacy_cutFactor_le n S B W D L)) 1

theorem legacy_growth_le (n S B W D L : ℕ) :
    IntegralMixedFullScriptHeight.growth n S B W D L ≤ growth n S B W D L :=
  Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right (legacy_coefficientFactor_le n S B W D L) 1)) 1

theorem legacy_height_le (n S B W D L C j : ℕ) :
    IntegralMixedFullScriptHeight.height n S B W D L C j ≤ height n S B W D L C j :=
  Nat.mul_le_mul_right (C+1) (Nat.pow_le_pow_left (legacy_growth_le n S B W D L) j)

end LeanCanny.Algebra.IntegralMixedLimitHeightProfile

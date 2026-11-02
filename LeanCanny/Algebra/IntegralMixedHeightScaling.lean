/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedAllRawHeightBounds
public import LeanCanny.Algebra.IntegralMixedCutBounds
/-! # Raw-cut and normalization height budgets grow linearly in input heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightScaling
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem affine_scaled (A C G : ℕ) (hG : 1 ≤ G) : A * G + C ≤ (A + C) * G := by
  calc
    _ ≤ A * G + C * G := Nat.add_le_add_left (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hG) _
    _ = _ := by ring

theorem coefficient_scaled (n M W D C V Q G : ℕ) (hG : 1 ≤ G) :
    IntegralFrozenCoefficientBounds.coefficientHeight n M W D (C * G) (V * G) (Q * G) ≤
      IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q * G := by
  let A := C + D * Q + n * (2 ^ W * (Q + V))
  let Z := IntegralFrozenCoefficientBounds.coefficientHeight n M W D 0 0 0
  calc
    _ = A * G + Z := by dsimp only [A, Z]; unfold IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight; ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by dsimp only [A, Z]; unfold IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight; ring

theorem lower_scaled (n M W D C V Q P G : ℕ) (hG : 1 ≤ G) :
    IntegralFrozenConstantBounds.lowerHeight n M W D (C * G) (V * G) (Q * G) (P * G) ≤
      IntegralFrozenConstantBounds.lowerHeight n M W D C V Q P * G := by
  let A := C + D * Q + n * (2 ^ W * (Q + V)) + P + D * V
  let Z := IntegralFrozenConstantBounds.lowerHeight n M W D 0 0 0 0
  calc
    _ = A * G + Z := by
      dsimp only [A, Z]
      unfold IntegralFrozenConstantBounds.lowerHeight IntegralFrozenConstantBounds.constantHeight IntegralFrozenConstantBounds.sumHeight
        IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight
      ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by
      dsimp only [A, Z]
      unfold IntegralFrozenConstantBounds.lowerHeight IntegralFrozenConstantBounds.constantHeight IntegralFrozenConstantBounds.sumHeight
        IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight
      ring

theorem determinant_scaled (n M H G : ℕ) (hG : 1 ≤ G) :
    IntegralRelativeCharacteristicBounds.determinantHeight n M (H * G) ≤
      IntegralRelativeCharacteristicBounds.determinantHeight n M H * G := by
  let A := n * H
  let Z := n * (M.size + n.size)
  calc
    _ = A * G + Z := by dsimp only [A, Z]; unfold IntegralRelativeCharacteristicBounds.determinantHeight; ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by dsimp only [A, Z]; unfold IntegralRelativeCharacteristicBounds.determinantHeight; ring

theorem gram_scaled (rows M H G : ℕ) (hG : 1 ≤ G) :
    IntegralMacaulayGramBounds.gramHeight rows M (H * G) ≤ IntegralMacaulayGramBounds.gramHeight rows M H * G := by
  let A := H + H
  let Z := M.size + rows.size
  calc
    _ = A * G + Z := by dsimp only [A, Z]; unfold IntegralMacaulayGramBounds.gramHeight; ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by dsimp only [A, Z]; unfold IntegralMacaulayGramBounds.gramHeight; ring

theorem principal_scaled (D M H G : ℕ) (hG : 1 ≤ G) :
    IntegralPrincipalHeightBounds.height D M (H * G) ≤ IntegralPrincipalHeightBounds.height D M H * G := by
  let A := H + 2 * D * H
  let Z := IntegralRelativeCharacteristicBounds.determinantHeight (2 * D) M D.size + M.size
  calc
    _ = A * G + Z := by dsimp only [A, Z]; unfold IntegralPrincipalHeightBounds.height IntegralRelativeCharacteristicBounds.determinantHeight; ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by dsimp only [A, Z]; unfold IntegralPrincipalHeightBounds.height IntegralRelativeCharacteristicBounds.determinantHeight; ring

theorem normalized_scaled (R H G : ℕ) (hG : 1 ≤ G) :
    IntegralMixedCutBounds.normalizedHeight R (H * G) ≤ IntegralMixedCutBounds.normalizedHeight R H * G := by
  let A := (3 * R + 1) * H
  let Z := IntegralMixedCutBounds.normalizedHeight R 0
  calc
    _ = A * G + Z := by
      dsimp only [A, Z]
      unfold IntegralMixedCutBounds.normalizedHeight IntegralInverseMatrixBounds.height IntegralInverseMatrixBounds.polynomialHeight CharacteristicIntegerBounds.budget
      ring
    _ ≤ (A + Z) * G := affine_scaled A Z G hG
    _ = _ := by
      dsimp only [A, Z]
      unfold IntegralMixedCutBounds.normalizedHeight IntegralInverseMatrixBounds.height IntegralInverseMatrixBounds.polynomialHeight CharacteristicIntegerBounds.budget
      ring
end LeanCanny.Algebra.IntegralMixedHeightScaling

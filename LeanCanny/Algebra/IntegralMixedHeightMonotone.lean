/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightScaling
/-! # Monotone original-metadata envelopes for mixed cut heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightScaling
open LeanCanny.Encoding LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem coefficient_mono {n N M R W Z D E C A V U Q T : ℕ}
    (hn : n ≤ N) (hM : M ≤ R) (hW : W ≤ Z) (hD : D ≤ E) (hC : C ≤ A) (hV : V ≤ U) (hQ : Q ≤ T) :
    IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q ≤
      IntegralFrozenCoefficientBounds.coefficientHeight N R Z E A U T := by
  unfold IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight
  gcongr <;> exact Nat.size_le_size hM

theorem lower_mono {n N M R W Z D E C A V U Q T P L : ℕ}
    (hn : n ≤ N) (hM : M ≤ R) (hW : W ≤ Z) (hD : D ≤ E) (hC : C ≤ A) (hV : V ≤ U) (hQ : Q ≤ T) (hP : P ≤ L) :
    IntegralFrozenConstantBounds.lowerHeight n M W D C V Q P ≤
      IntegralFrozenConstantBounds.lowerHeight N R Z E A U T L := by
  unfold IntegralFrozenConstantBounds.lowerHeight IntegralFrozenConstantBounds.constantHeight IntegralFrozenConstantBounds.sumHeight
  exact Nat.add_le_add_right
    (Nat.add_le_add (coefficient_mono hn hM hW hD hC hV hQ)
      (Nat.add_le_add hP (Nat.add_le_add (Nat.mul_le_mul hD (Nat.add_le_add hV (Nat.size_le_size hM))) (Nat.size_le_size hn)))) 1

theorem determinant_mono {n N M R H G : ℕ} (hn : n ≤ N) (hM : M ≤ R) (hH : H ≤ G) :
    IntegralRelativeCharacteristicBounds.determinantHeight n M H ≤ IntegralRelativeCharacteristicBounds.determinantHeight N R G := by
  unfold IntegralRelativeCharacteristicBounds.determinantHeight
  exact Nat.mul_le_mul hn (Nat.add_le_add (Nat.add_le_add hH (Nat.size_le_size hM)) (Nat.size_le_size hn))

theorem gram_mono {m N R S H G : ℕ} (hm : m ≤ N) (hR : R ≤ S) (hH : H ≤ G) :
    IntegralMacaulayGramBounds.gramHeight m R H ≤ IntegralMacaulayGramBounds.gramHeight N S G := by
  unfold IntegralMacaulayGramBounds.gramHeight
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hH hH) (Nat.size_le_size hR)) (Nat.size_le_size hm)

theorem normalized_mono {r R h H : ℕ} (hr : r ≤ R) (hh : h ≤ H) :
    IntegralMixedCutBounds.normalizedHeight r h ≤ IntegralMixedCutBounds.normalizedHeight R H := by
  unfold IntegralMixedCutBounds.normalizedHeight IntegralInverseMatrixBounds.height IntegralInverseMatrixBounds.polynomialHeight CharacteristicIntegerBounds.budget
  gcongr <;> first | exact Nat.size_le_size hr | exact Nat.size_le_size (Nat.add_le_add_right hr 1)

theorem boxWidth_mono {n d D : ℕ} (hd : d ≤ D) :
    IntegralMixedExceptionalBounds.boxWidth n d ≤ IntegralMixedExceptionalBounds.boxWidth n D := by
  unfold IntegralMixedExceptionalBounds.boxWidth IntegralMixedExceptionalBounds.boxBase
  apply Nat.size_le_size
  have HK := IntegralCriticalFactorCeiling.dimension_mono (Nat.le_refl n) hd
  exact Nat.add_le_add_right (Nat.add_le_add hd (Nat.mul_le_mul_left n HK)) 1
end LeanCanny.Algebra.IntegralMixedHeightScaling

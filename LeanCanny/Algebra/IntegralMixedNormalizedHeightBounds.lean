/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCutBounds
public import LeanCanny.Algebra.IntegralMixedHeightMonotone

/-! # Generic normalized scalar height estimates over the retained prefix

These estimates apply to an actual relative polynomial before it receives a
history tag. Singular top matrices use the existing characteristic inverse
normalization; no field inverse or evaluator is supplied.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedHeightBounds
open LeanCanny.Encoding FixedWidthPolynomial UniformIntegralPrefix IntegralMixedHistory
open IntegralRelativeNormalizationMatrix IntegralRelativeLeadingNormalization
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem leading_height (x : State P S B m ι) (p : Polynomial x.sampler.scalarPrefix.carrier) (d H : ℕ)
    (hH : ∀ k i j, (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (p.coeff k) i j).natAbs ≤ 2^H) :
    (normalizedScalarLeading x p d).natAbs ≤ 2^CharacteristicIntegerBounds.budget (count m B) H :=
  IntegralInverseMatrixBounds.denominator_height _ H (hH d)

theorem coefficient_height (x : State P S B m ι) (p : Polynomial x.sampler.scalarPrefix.carrier) (d H : ℕ)
    (hH : ∀ k i j, (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (p.coeff k) i j).natAbs ≤ 2^H)
    (k : ℕ) (i j : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((normalizedScalarPolynomial x p d).coeff k) i j).natAbs ≤
        2^IntegralMixedCutBounds.normalizedHeight (count m B) H := by
  rw [normalizedScalarPolynomial,matrix_eq]
  split_ifs with HK
  · simp only [Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact (leading_height x p d H hH).trans (Nat.pow_le_pow_right (by decide)
        (by unfold IntegralMixedCutBounds.normalizedHeight; omega))
    · simp only [mul_zero,Int.natAbs_zero,Nat.zero_le]
  · have HM := IntegralParameterMatrixBounds.mul_height
      (inverseMatrix x.sampler.scalarPrefix.basis.finBasis p d)
      (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (p.coeff k))
      (IntegralInverseMatrixBounds.height (count m B) H) H
      (IntegralInverseMatrixBounds.inverse_height _ H (hH d)) (hH k) i j
    exact HM.trans (Nat.pow_le_pow_right (by decide) (by unfold IntegralMixedCutBounds.normalizedHeight; omega))

variable [Fintype ι]

theorem step_bounds (x : State P S B m ι) (hm : m ≤ S)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (d G H : ℕ) (hG : x.bank.Bounds G)
    (hH : ∀ k i j, (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (p.coeff k) i j).natAbs ≤ 2^H) :
    (normalizedScalarStep x hm p d).bank.Bounds
      (max G (bankStepHeight (count m B) (2^B) (IntegralMixedCutBounds.normalizedHeight (count m B) H))) := by
  apply x.bank.rootStep_bounds hm _ d _ G _ hG (coefficient_height x p d H hH)
  exact (leading_height x p d H hH).trans (Nat.pow_le_pow_right (by decide)
    (by unfold IntegralMixedCutBounds.normalizedHeight; omega))

theorem scaled_step_bounds (x : State P S B m ι) (hm : m ≤ S)
    (p : Polynomial x.sampler.scalarPrefix.carrier) (d G R K : ℕ)
    (hG : x.bank.Bounds G) (hG1 : 1 ≤ G) (hR : count m B ≤ R)
    (hH : ∀ k i j, (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis (p.coeff k) i j).natAbs ≤ 2^(K*G)) :
    (normalizedScalarStep x hm p d).bank.Bounds
      (bankGrowth R (2^B) (IntegralMixedCutBounds.normalizedHeight R K)*G) := by
  have HN := (IntegralMixedHeightScaling.normalized_mono hR (Nat.le_refl (K*G))).trans
    (IntegralMixedHeightScaling.normalized_scaled R K G hG1)
  apply x.bank.rootStep_scaled_bounds hm _ d (IntegralMixedCutBounds.normalizedHeight (count m B) (K*G)) G R
    (IntegralMixedCutBounds.normalizedHeight R K) _ hG hG1 hR HN
  · exact coefficient_height x p d (K*G) hH
  · exact (leading_height x p d (K*G) hH).trans (Nat.pow_le_pow_right (by decide)
      (by unfold IntegralMixedCutBounds.normalizedHeight; omega))

end LeanCanny.Algebra.IntegralMixedNormalizedHeightBounds

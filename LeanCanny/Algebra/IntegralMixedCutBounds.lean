/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCutMatrix
public import LeanCanny.Algebra.IntegralInverseMatrixBounds
public import LeanCanny.Algebra.IntegralScalarRootHeightBank

/-! # Derived normalization and bank budgets for actual relative cuts

Only the literal raw factor coefficient matrices need a height allowance.
The integer leading, normalized coefficients and actual retained bank
budgets are then derived, including singular top-coefficient matrices.
These bounds do not change the original spatial or scalar degree cap.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutBounds
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts IntegralMixedCutMatrix
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial
open scoped Classical

def normalizedHeight (R H : ℕ) :=
  CharacteristicIntegerBounds.budget R H + IntegralInverseMatrixBounds.height R H + H + R.size

theorem normalizedHeight_binary {R H : List Bool → ℕ} (hR : BinaryFn R) (hH : BinaryFn H) :
    BinaryFn (fun q => normalizedHeight (R q) (H q)) :=
  (((CharacteristicIntegerBounds.budget_binary hR hH).add
    (IntegralInverseMatrixBounds.height_binary hR hH)).add hH).add hR.size

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem leading_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n) (c : Kind P r)
    (d H : ℕ) (hH : ∀ k i j, (coefficientMatrix x hm r c k i j).natAbs ≤ 2 ^ H) :
    (normalizedScalarLeading x (raw x hm r c d) d).natAbs ≤
      2 ^ CharacteristicIntegerBounds.budget (count m B) H := by
  rw [leading_eq]
  exact IntegralInverseMatrixBounds.denominator_height _ H (hH d)

theorem normalized_coefficient_height (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d H : ℕ)
    (hH : ∀ k i j, (coefficientMatrix x hm r c k i j).natAbs ≤ 2 ^ H)
    (k : ℕ) (i j : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((normalizedScalarPolynomial x (raw x hm r c d) d).coeff k) i j).natAbs ≤
        2 ^ normalizedHeight (count m B) H := by
  rw [normalized_coefficient_matrix]
  split_ifs with HD HK
  · simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs
    · rw [mul_one]
      exact (leading_height x hm r c d H hH).trans
        (Nat.pow_le_pow_right (by decide) (by unfold normalizedHeight; omega))
    · simp only [mul_zero, Int.natAbs_zero, Nat.zero_le]
  · have HM := IntegralParameterMatrixBounds.mul_height
      (Polynomial.aeval (coefficientMatrix x hm r c d)
        (IntegralParameterInverse.inverse (coefficientMatrix x hm r c d).charpoly))
      (coefficientMatrix x hm r c k) (IntegralInverseMatrixBounds.height (count m B) H) H
      (IntegralInverseMatrixBounds.inverse_height _ H (hH d)) (hH k) i j
    exact HM.trans (Nat.pow_le_pow_right (by decide) (by unfold normalizedHeight; omega))
  · simp only [Matrix.zero_apply, Int.natAbs_zero, Nat.zero_le]

variable [Fintype ι]

theorem step_bank_bounds (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (c : Kind P r) (d G H : ℕ) (hG : x.bank.Bounds G)
    (hH : ∀ k i j, (coefficientMatrix x hm r c k i j).natAbs ≤ 2 ^ H) :
    (step x hm r c d).bank.Bounds
      (max G (UniformIntegralPrefix.bankStepHeight (count m B) (2 ^ B)
        (normalizedHeight (count m B) H))) := by
  apply x.bank.rootStep_bounds hm _ _ _ G _ hG
    (normalized_coefficient_height x hm r c d H hH)
  exact (leading_height x hm r c d H hH).trans
    (Nat.pow_le_pow_right (by decide) (by unfold normalizedHeight; omega))

end LeanCanny.Algebra.IntegralMixedCutBounds

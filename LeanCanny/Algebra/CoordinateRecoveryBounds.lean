/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateRecovery
public import LeanCanny.Algebra.SubresultantRecoveryBounds

/-!
# Coordinate-recovery output bounds across all degree cases

The direct linear branches have parameter degree at most one. Together with
the interior subresultant estimates this gives uniform degree and integer
coefficient bit bounds, without hypotheses on roots or separability.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

theorem coordinateCoefficient_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c r : ℕ) :
    (coordinateCoefficient p₁ p₂ c r).natDegree ≤ max 1 ((p₂.natDegree - 1) * p₁.natDegree) := by
  unfold coordinateCoefficient
  split_ifs with hn hm
  · simp
  · have hs := shiftFamily_coeff_natDegree_le p₁ c r
    have he : ((shiftFamily p₁ c).coeff r).natDegree ≤ 1 := by omega
    exact he.trans (le_max_left _ _)
  · exact (recoverySubresultant_coeff_natDegree_le p₁ p₂ c r).trans (le_max_right _ _)

theorem coordinateNumerator_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (coordinateNumerator p₁ p₂ c).natDegree ≤ max 1 ((p₂.natDegree - 1) * p₁.natDegree) :=
  coordinateCoefficient_natDegree_le p₁ p₂ c 0

theorem coordinateDenominator_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (coordinateDenominator p₁ p₂ c).natDegree ≤ max 1 ((p₂.natDegree - 1) * p₁.natDegree) :=
  coordinateCoefficient_natDegree_le p₁ p₂ c 1

def coordinateBitBudget (m n c H₁ H₂ : ℕ) : ℕ :=
  Subresultant.budget m n 1 (shiftBitBudget m c H₁) H₂.size + shiftBitBudget m c H₁ + H₂.size + 1

theorem coordinateCoefficient_coeff_size_le (p₁ p₂ : Polynomial ℤ) (c H₁ H₂ r d : ℕ)
    (h₁ : ∀ i, (p₁.coeff i).natAbs ≤ H₁) (h₂ : ∀ i, (p₂.coeff i).natAbs ≤ H₂) :
    ((coordinateCoefficient p₁ p₂ c r).coeff d).natAbs.size ≤
      coordinateBitBudget p₁.natDegree p₂.natDegree c H₁ H₂ := by
  unfold coordinateCoefficient
  split_ifs with hn hm
  · rw [Polynomial.coeff_C]
    split_ifs
    · have he := Nat.size_le_size (h₂ r)
      unfold coordinateBitBudget
      omega
    · simp
  · have hs := shiftFamily_coeff_size_le p₁ c H₁ r d h₁
    unfold coordinateBitBudget shiftBitBudget
    omega
  · have hs := recoverySubresultant_coeff_coeff_size_le p₁ p₂ c H₁ H₂ r d h₁ h₂
    unfold coordinateBitBudget
    omega

end LeanCanny.Algebra

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SubresultantRecovery
public import LeanCanny.Algebra.SubresultantBounds
public import LeanCanny.Algebra.ResultantBounds

/-!
# Output bounds for Canny's symbolic subresultant recovery

Both coordinate-recovery polynomials have degree at most `(d₂-1)*d₁`.
Their integer coefficients satisfy the reduced-column determinant bit budget,
with no nonzero, splitting, separability, or direction assumptions.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

theorem recoverySubresultant_coeff_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c r : ℕ) :
    ((recoverySubresultant p₁ p₂ c).coeff r).natDegree ≤ (p₂.natDegree - 1) * p₁.natDegree := by
  have hf : ∀ i, ((shiftFamily p₁ c).coeff i).natDegree ≤ p₁.natDegree := fun i =>
    (shiftFamily_coeff_natDegree_le p₁ c i).trans (Nat.sub_le _ _)
  have hg : ∀ i, ((p₂.map C).coeff i).natDegree ≤ 0 := by simp
  simpa only [recoverySubresultant, Nat.mul_zero, Nat.zero_add] using
    Subresultant.coeff_natDegree_le (shiftFamily p₁ c) (p₂.map C)
      p₁.natDegree p₂.natDegree 1 r p₁.natDegree 0 hf hg

theorem subresultantNumerator_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (subresultantNumerator p₁ p₂ c).natDegree ≤ (p₂.natDegree - 1) * p₁.natDegree :=
  recoverySubresultant_coeff_natDegree_le p₁ p₂ c 0

theorem subresultantDenominator_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (subresultantDenominator p₁ p₂ c).natDegree ≤ (p₂.natDegree - 1) * p₁.natDegree :=
  recoverySubresultant_coeff_natDegree_le p₁ p₂ c 1

theorem recoverySubresultant_coeff_coeff_size_le (p₁ p₂ : Polynomial ℤ) (c H₁ H₂ r d : ℕ)
    (h₁ : ∀ i, (p₁.coeff i).natAbs ≤ H₁) (h₂ : ∀ i, (p₂.coeff i).natAbs ≤ H₂) :
    (((recoverySubresultant p₁ p₂ c).coeff r).coeff d).natAbs.size ≤
      Subresultant.budget p₁.natDegree p₂.natDegree 1 (shiftBitBudget p₁.natDegree c H₁) H₂.size := by
  have hf : ∀ i, coefficientMass ((shiftFamily p₁ c).coeff i) ≤
      2 ^ shiftBitBudget p₁.natDegree c H₁ := fun i =>
    (shiftFamily_coeff_mass_le p₁ c H₁ i h₁).trans (shiftMassBound_le_two_pow _ _ _)
  have hg : ∀ i, coefficientMass ((p₂.map C).coeff i) ≤ 2 ^ H₂.size := by
    intro i
    simpa only [Polynomial.coeff_map, coefficientMass_C] using (h₂ i).trans (Nat.lt_size_self H₂).le
  exact Subresultant.coeff_coeff_size_le (shiftFamily p₁ c) (p₂.map C)
    p₁.natDegree p₂.natDegree 1 r (shiftBitBudget p₁.natDegree c H₁) H₂.size d hf hg

end LeanCanny.Algebra

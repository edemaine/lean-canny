/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoefficientBounds
public import LeanCanny.Algebra.ShiftCoefficients

/-!
# Coefficient lengths of Canny's integer resultant

The Sylvester determinant has `d₂` columns from `p₁(θ-c*x)` and `d₁` columns
from the constant-coefficient polynomial `p₂(x)`. Keeping these two allowances
separate gives a bound on every integer coefficient without constructing the
matrix or enumerating its permutations. No separability or nonzero hypotheses
are needed for the estimates.

The results concern the unnormalized integer resultant. Scalar normalization
over a field, encoded determinant computation, and workspace bounds are separate.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

/-- The determinant specification has degree at most `d₁*d₂` over any
commutative ring, without splitting, nonzero, or square-free assumptions. -/
theorem projectionResultant_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (projectionResultant p₁ p₂ c).natDegree ≤ p₁.natDegree * p₂.natDegree := by
  have hf : ∀ i, ((p₂.map C).coeff i).natDegree ≤ 0 := by simp
  have hg : ∀ i, ((shiftFamily p₁ c).coeff i).natDegree ≤ p₁.natDegree := fun i =>
    (shiftFamily_coeff_natDegree_le p₁ c i).trans (Nat.sub_le _ _)
  simpa only [projectionResultant, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.mul_comm] using
    resultant_natDegree_le (p₂.map C) (shiftFamily p₁ c)
      p₂.natDegree p₁.natDegree 0 p₁.natDegree hf hg

theorem cannyResultant_natDegree_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (cannyResultant p₁ p₂ c).natDegree ≤ p₁.natDegree * p₂.natDegree := by
  rw [cannyResultant_eq_sign_mul]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (projectionResultant_natDegree_le p₁ p₂ c)

theorem cannyResultant_card_support_le {R : Type*} [CommRing R]
    (p₁ p₂ : Polynomial R) (c : ℕ) :
    (cannyResultant p₁ p₂ c).support.card ≤ p₁.natDegree * p₂.natDegree + 1 :=
  (Polynomial.card_supp_le_succ_natDegree _).trans
    (Nat.add_le_add_right (cannyResultant_natDegree_le p₁ p₂ c) 1)

/-- A coefficient-mass allowance for one coefficient of the shifted family. -/
def shiftMassBound (d c H : ℕ) : ℕ :=
  (d + 1) * (2 ^ d * H * (c + 1) ^ d)

/-- An exponent bounding `shiftMassBound` by a power of two. -/
def shiftBitBudget (d c H : ℕ) : ℕ :=
  (d + 1).size + d + H.size + (c + 1).size * d

theorem shiftMassBound_le_two_pow (d c H : ℕ) :
    shiftMassBound d c H ≤ 2 ^ shiftBitBudget d c H := by
  unfold shiftMassBound shiftBitBudget
  calc
    _ ≤ 2 ^ (d + 1).size * (2 ^ d * 2 ^ H.size * (2 ^ (c + 1).size) ^ d) :=
      Nat.mul_le_mul (Nat.lt_size_self _).le
        (Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.lt_size_self H).le)
          (Nat.pow_le_pow_left (Nat.lt_size_self (c + 1)).le d))
    _ = _ := by simp only [← pow_mul, ← pow_add]; congr 1; omega

theorem shiftFamily_coeff_mass_le (p : Polynomial ℤ) (c H i : ℕ)
    (hH : ∀ k, (p.coeff k).natAbs ≤ H) :
    coefficientMass ((shiftFamily p c).coeff i) ≤ shiftMassBound p.natDegree c H :=
  coefficientMass_le _ _ _
    ((shiftFamily_coeff_natDegree_le p c i).trans (Nat.sub_le _ _))
    (shiftFamily_coeff_natAbs_le p c H i · hH)

theorem projectionResultant_coeff_natAbs_le (p₁ p₂ : Polynomial ℤ) (c H₁ H₂ k : ℕ)
    (h₁ : ∀ i, (p₁.coeff i).natAbs ≤ H₁)
    (h₂ : ∀ i, (p₂.coeff i).natAbs ≤ H₂) :
    ((projectionResultant p₁ p₂ c).coeff k).natAbs ≤
      (p₁.natDegree + p₂.natDegree).factorial *
        (shiftMassBound p₁.natDegree c H₁ ^ p₂.natDegree * H₂ ^ p₁.natDegree) := by
  have hf : ∀ i, coefficientMass ((p₂.map C).coeff i) ≤ H₂ := by
    intro i
    simpa only [Polynomial.coeff_map, coefficientMass_C] using h₂ i
  have h := resultant_coeff_natAbs_le (p₂.map C) (shiftFamily p₁ c)
    p₂.natDegree p₁.natDegree H₂ (shiftMassBound p₁.natDegree c H₁)
    hf (fun i => shiftFamily_coeff_mass_le p₁ c H₁ i h₁) k
  simpa only [projectionResultant, Nat.add_comm p₂.natDegree] using h

/-- An explicit output coefficient length bound in the source degrees, their
binary lengths, the direction's binary length, and the input coefficient lengths. -/
theorem projectionResultant_coeff_size_le (p₁ p₂ : Polynomial ℤ) (c H₁ H₂ k : ℕ)
    (h₁ : ∀ i, (p₁.coeff i).natAbs ≤ H₁)
    (h₂ : ∀ i, (p₂.coeff i).natAbs ≤ H₂) :
    ((projectionResultant p₁ p₂ c).coeff k).natAbs.size ≤
      (p₁.natDegree + p₂.natDegree).size * (p₁.natDegree + p₂.natDegree) +
        p₂.natDegree * shiftBitBudget p₁.natDegree c H₁ + p₁.natDegree * H₂.size + 1 := by
  have hf : ∀ i, coefficientMass ((p₂.map C).coeff i) ≤ 2 ^ H₂.size := by
    intro i
    simpa only [Polynomial.coeff_map, coefficientMass_C] using
      (h₂ i).trans (Nat.lt_size_self H₂).le
  have hg : ∀ i, coefficientMass ((shiftFamily p₁ c).coeff i) ≤
      2 ^ shiftBitBudget p₁.natDegree c H₁ := fun i =>
    (shiftFamily_coeff_mass_le p₁ c H₁ i h₁).trans (shiftMassBound_le_two_pow _ _ _)
  have h := resultant_coeff_size_le (p₂.map C) (shiftFamily p₁ c)
    p₂.natDegree p₁.natDegree H₂.size (shiftBitBudget p₁.natDegree c H₁) hf hg k
  simpa only [projectionResultant, Nat.add_comm p₂.natDegree] using h

/-- Swapping the resultant inputs changes only a sign, including for zero
polynomials and degree-zero inputs. -/
theorem cannyResultant_coeff_natAbs (p₁ p₂ : Polynomial ℤ) (c k : ℕ) :
    ((cannyResultant p₁ p₂ c).coeff k).natAbs =
      ((projectionResultant p₁ p₂ c).coeff k).natAbs := by
  rw [cannyResultant_eq_sign_mul, Polynomial.coeff_C_mul]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]

theorem cannyResultant_coeff_size_le (p₁ p₂ : Polynomial ℤ) (c H₁ H₂ k : ℕ)
    (h₁ : ∀ i, (p₁.coeff i).natAbs ≤ H₁)
    (h₂ : ∀ i, (p₂.coeff i).natAbs ≤ H₂) :
    ((cannyResultant p₁ p₂ c).coeff k).natAbs.size ≤
      (p₁.natDegree + p₂.natDegree).size * (p₁.natDegree + p₂.natDegree) +
        p₂.natDegree * shiftBitBudget p₁.natDegree c H₁ + p₁.natDegree * H₂.size + 1 := by
  rw [cannyResultant_coeff_natAbs]
  exact projectionResultant_coeff_size_le p₁ p₂ c H₁ H₂ k h₁ h₂

end LeanCanny.Algebra

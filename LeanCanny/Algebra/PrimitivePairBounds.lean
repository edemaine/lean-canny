/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairCoordinates
public import LeanCanny.Algebra.CoefficientMass
public import LeanCanny.Algebra.LinearCoefficientBounds

/-! # Coefficient-mass budgets for the explicit integer pair coordinates

The common mass exponent comes from the existing subresultant coefficient
budget, its degree allowance, and the binary size of the shear direction.
No algebraic-root assumptions are needed for these arithmetic bounds.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePair
open Polynomial

def massBudget (m n c H₁ H₂ : ℕ) : ℕ :=
  coordinateBitBudget m n c H₁ H₂ + (max 1 ((n - 1) * m) + 1).size + c.size

theorem coordinate_mass (p q : ℤ[X]) (c H₁ H₂ : ℕ)
    (hp : ∀ k, (p.coeff k).natAbs ≤ H₁) (hq : ∀ k, (q.coeff k).natAbs ≤ H₂) :
    coefficientMass (leftNumerator p q c) ≤ 2 ^ massBudget p.natDegree q.natDegree c H₁ H₂ ∧
      coefficientMass (rightNumerator p q c) ≤ 2 ^ massBudget p.natDegree q.natDegree c H₁ H₂ ∧
      coefficientMass (denominator p q c) ≤ 2 ^ massBudget p.natDegree q.natDegree c H₁ H₂ := by
  let b := coordinateBitBudget p.natDegree q.natDegree c H₁ H₂
  let G := max 1 ((q.natDegree - 1) * p.natDegree)
  let B := b + (G + 1).size
  have hc (r k : ℕ) : ((coordinateCoefficient p q c r).coeff k).natAbs ≤ 2 ^ b :=
    (Nat.size_le.mp (coordinateCoefficient_coeff_size_le p q c H₁ H₂ r k hp hq)).le
  have hn : coefficientMass (coordinateNumerator p q c) ≤ 2 ^ B :=
    coefficientMass_le_pow_of_degree_coeff _ G b (coordinateNumerator_natDegree_le p q c) (hc 0)
  have hd : coefficientMass (denominator p q c) ≤ 2 ^ B :=
    coefficientMass_le_pow_of_degree_coeff _ G b (denominator_degree p q c) (hc 1)
  have hpow : 2 ^ B ≤ 2 ^ (B + c.size) := Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)
  have hleft : coefficientMass (leftNumerator p q c) ≤ (c + 1) * 2 ^ B := by
    apply (coefficientMass_add_le _ _).trans
    have hx : coefficientMass (X : ℤ[X]) = 1 := by simpa only [pow_one] using coefficientMass_X_pow 1
    have hX := coefficientMass_mul_le (X : ℤ[X]) (denominator p q c)
    rw [hx, one_mul] at hX
    have hXD := hX.trans hd
    have hC := coefficientMass_mul_le (C (c : ℤ)) (coordinateNumerator p q c)
    rw [coefficientMass_C, Int.natAbs_natCast] at hC
    have hCN := hC.trans (Nat.mul_le_mul_left c hn)
    exact (Nat.add_le_add hXD hCN).trans_eq (by ring)
  have hfinal : (c + 1) * 2 ^ B ≤ 2 ^ (B + c.size) := by
    calc
      _ ≤ 2 ^ c.size * 2 ^ B := Nat.mul_le_mul_right _ (Nat.lt_size_self c)
      _ = _ := by rw [← pow_add, Nat.add_comm]
  refine ⟨hleft.trans hfinal, ?_, hd.trans hpow⟩
  rw [rightNumerator, coefficientMass_neg]
  exact hn.trans hpow

end LeanCanny.Algebra.PrimitivePair

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ParameterMatrixMassBounds
public import LeanCanny.Algebra.PrincipalParameterMass
public import LeanCanny.Algebra.ScaledPolynomialQuotient
public import LeanCanny.Algebra.NestedCoefficientMass

/-! # Mass of the actual padded characteristic quotient

The Cramer determinant bounds the quotient before parameter evaluation. The
estimate needs only input matrix entry masses, including when the extraneous
determinant vanishes at zero. No division by that determinant occurs.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedCharacteristicQuotientMass
open Polynomial ParameterMatrixMassBounds
open scoped Classical

def inputBudget (N r H : ℕ) := characteristicBudget N H + (N + 1).size + r

def budget (N r H : ℕ) := (r + 1).size * (r + 1) + (r + 1) * inputBudget N r H

theorem budget_binary {N r H : List Bool → ℕ}
    (hN : BinaryFn N) (hr : BinaryFn r) (hH : BinaryFn H) :
    BinaryFn (fun q => budget (N q) (r q) (H q)) := by
  have ht := hr.add (BinaryFn.const 1)
  exact (ht.size.mul ht).add (ht.mul
    (((characteristicBudget_binary hN hH).add (hN.add (BinaryFn.const 1)).size).add hr))

private theorem padding_mass (r : ℕ) :
    NestedMass.mass ((1 - X : (ℤ[X])[X]) ^ r) ≤ 2 ^ r := by
  have h : NestedMass.mass (1 - X : (ℤ[X])[X]) ≤ 2 := by
    have hOne : NestedMass.mass (1 : (ℤ[X])[X]) = 1 := by
      change NestedMass.mass (Polynomial.C (Polynomial.C (1 : ℤ))) = 1
      rw [NestedMass.C, coefficientMass_C]
      rfl
    have hX : NestedMass.mass (X : (ℤ[X])[X]) = 1 := by
      rw [← Polynomial.monomial_one_one_eq_X, NestedMass.monomial]
      change coefficientMass (Polynomial.C (1 : ℤ)) = 1
      rw [coefficientMass_C]
      rfl
    simpa only [hOne, hX] using NestedMass.sub_le (1 : (ℤ[X])[X]) X
  exact (NestedMass.pow_le _ r).trans (Nat.pow_le_pow_left h r)

theorem coefficient (N r H : ℕ) (A E : Matrix (Fin N) (Fin N) ℤ[X])
    (hA : ∀ i j, coefficientMass (A i j) ≤ 2 ^ H)
    (hE : ∀ i j, coefficientMass (E i j) ≤ 2 ^ H) (k : ℕ) :
    coefficientMass ((ScaledPolynomialQuotient.quotient E.charpoly
      (A.charpoly * (1 - X) ^ r) N r).coeff k) ≤ 2 ^ budget N r H := by
  have hD : ∀ j, coefficientMass (E.charpoly.coeff j) ≤ 2 ^ inputBudget N r H := by
    intro j
    apply (charpoly_coefficient_mass E H hE j).trans
    apply Nat.pow_le_pow_right (by decide)
    simp only [Fintype.card_fin, inputBudget]
    omega
  have hG : ∀ j, coefficientMass ((A.charpoly * (1 - X) ^ r).coeff j) ≤
      2 ^ inputBudget N r H := by
    have hc : NestedMass.mass A.charpoly ≤ 2 ^ (characteristicBudget N H + (N + 1).size) := by
      apply NestedMass.le_pow A.charpoly N (characteristicBudget N H)
      · simpa only [Fintype.card_fin] using (Matrix.charpoly_natDegree_eq_dim A).le
      · intro j
        simpa only [Fintype.card_fin] using charpoly_coefficient_mass A H hA j
    intro j
    calc
      _ ≤ NestedMass.mass (A.charpoly * (1 - X) ^ r) := NestedMass.coeff_le _ _
      _ ≤ NestedMass.mass A.charpoly * NestedMass.mass ((1 - X) ^ r) := NestedMass.mul_le _ _
      _ ≤ 2 ^ (characteristicBudget N H + (N + 1).size) * 2 ^ r :=
        Nat.mul_le_mul hc (padding_mass r)
      _ = _ := by rw [← pow_add]; rfl
  rw [ScaledPolynomialQuotient.quotient_coeff]
  split_ifs with hk
  · have hd := det_coefficientMass_le_pow
      ((ScaledPolynomialQuotient.matrix E.charpoly N r).updateCol ⟨k, hk⟩
        (ScaledPolynomialQuotient.input (A.charpoly * (1 - X) ^ r) N r))
      (inputBudget N r H) (fun i j => ?_)
    · simpa only [Fintype.card_fin, budget] using hd
    · rw [ScaledPolynomialQuotient.selected_entry]
      split_ifs
      · exact hG _
      · exact hD _
      · simp
  · simp

end LeanCanny.Algebra.PaddedCharacteristicQuotientMass

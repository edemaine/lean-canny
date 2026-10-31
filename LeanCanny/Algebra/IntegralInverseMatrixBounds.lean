/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralParameterMatrixBounds
public import LeanCanny.Algebra.IntegralParameterInverse
public import LeanCanny.Algebra.MatrixPolynomialEntryCorrect

/-! # Binary height bounds for constructed inverse-polynomial matrices

The inverse polynomial strips zero characteristic roots; its bounds also
apply to singular matrices. Polynomial evaluation adds matrix-power and
summation budgets, all computable from the original entry-height bound.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralInverseMatrixBounds
open LeanCanny.Encoding Polynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

def polynomialHeight (n D C H : ℕ) : ℕ := C + D * (H + n.size) + (D + 1).size

theorem polynomial_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : Polynomial ℤ) (D C H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (hp : p.natDegree ≤ D)
    (hc : ∀ k, (p.coeff k).natAbs ≤ 2 ^ C) (i j : Fin n) :
    ((p.eval₂ (Matrix.scalar (Fin n)) A) i j).natAbs ≤ 2 ^ polynomialHeight n D C H := by
  rw [MatrixPolynomialEntryBits.polynomial_entry p A (D + 1) (by omega)]
  calc
    _ ≤ ∑ k ∈ Finset.range (D + 1), (p.coeff k * (A ^ k) i j).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (D + 1), 2 ^ (C + D * (H + n.size)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Int.natAbs_mul]
      have HK : k ≤ D := by have := Finset.mem_range.mp hk; omega
      calc
        _ ≤ 2 ^ C * 2 ^ (k * (H + n.size)) :=
          Nat.mul_le_mul (hc k) (IntegralParameterMatrixBounds.pow_height A H hA k i j)
        _ = 2 ^ (C + k * (H + n.size)) := (pow_add _ _ _).symm
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_right _ HK) C)
    _ = (D + 1) * 2 ^ (C + D * (H + n.size)) := by simp
    _ ≤ 2 ^ (D + 1).size * 2 ^ (C + D * (H + n.size)) :=
      Nat.mul_le_mul_right _ (Nat.lt_size_self (D + 1)).le
    _ = _ := by rw [← pow_add, polynomialHeight]; congr 1; omega

def height (n H : ℕ) : ℕ := polynomialHeight n n (CharacteristicIntegerBounds.budget n H) H

theorem height_binary {n H : List Bool → ℕ} (hn : BinaryFn n) (hH : BinaryFn H) :
    BinaryFn (fun c => height (n c) (H c)) :=
  ((CharacteristicIntegerBounds.budget_binary hn hH).add (hn.mul (hH.add hn.size))).add
    (hn.add (BinaryFn.const 1)).size

theorem characteristic_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (k : ℕ) :
    (A.charpoly.coeff k).natAbs ≤ 2 ^ CharacteristicIntegerBounds.budget n H :=
  (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide)
    (CharacteristicIntegerBounds.coefficient_bits A H hA k))

theorem inverse_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) (i j : Fin n) :
    (Polynomial.aeval A (IntegralParameterInverse.inverse A.charpoly) i j).natAbs ≤ 2 ^ height n H := by
  have HD : (IntegralParameterInverse.inverse A.charpoly).natDegree ≤ n := by
    simpa only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] using
      IntegralParameterInverse.natDegree_inverse_le A.charpoly
  have HC := IntegralParameterInverse.inverse_coefficient_bound A.charpoly
    (2 ^ CharacteristicIntegerBounds.budget n H) (characteristic_height A H hA)
  have HS : algebraMap ℤ (Matrix (Fin n) (Fin n) ℤ) = Matrix.scalar (Fin n) := Subsingleton.elim _ _
  simpa only [Polynomial.aeval_def, HS, height] using
    polynomial_height A (IntegralParameterInverse.inverse A.charpoly) n (CharacteristicIntegerBounds.budget n H) H hA HD HC i j

theorem denominator_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (H : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ H) :
    (IntegralParameterInverse.denominator A.charpoly).natAbs ≤ 2 ^ CharacteristicIntegerBounds.budget n H :=
  IntegralParameterInverse.denominator_bound A.charpoly _ (characteristic_height A H hA)

end LeanCanny.Algebra.IntegralInverseMatrixBounds

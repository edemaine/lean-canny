/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCoordinateEliminant
public import Mathlib.Data.Nat.Size

/-! # Binary size of the coercive coordinate radius

The radius exponent uses only the dimension, a degree allowance, and a
coefficient-mass exponent. Its binary length is polynomial in these input
lengths, even though the radius itself may be doubly exponential.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveRadiusBits
open CoerciveCoordinateEliminant CoerciveCriticalHomogenization
open scoped BigOperators

private theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

private theorem size_mul_le (a b : ℕ) : (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (pow_pos (by decide) _))

private theorem size_add_le (a b : ℕ) : (a + b).size ≤ a.size + b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (a.size + b.size) := (Nat.lt_size_self a).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb : b < 2 ^ (a.size + b.size) := (Nat.lt_size_self b).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

/-- Binary width of one Macaulay exponent block. -/
theorem width_le (n D : ℕ) : width n D ≤ n + D.size + 3 := by
  have hlevel : Macaulay.level (finDegree (n := n) D) ≤ (n + 1) * (2 * D + 1) := by
    unfold Macaulay.level
    have hsum : (∑ j : Fin (n + 1), (finDegree D j - 1)) ≤ (n + 1) * (2 * D) := by
      calc
        _ ≤ ∑ _j : Fin (n + 1), 2 * D := Finset.sum_le_sum (fun j _ => by have h := finDegree_le D j; omega)
        _ = _ := by simp [Nat.mul_comm]
    nlinarith
  have hmax : max (Macaulay.level (finDegree (n := n) D)) (2 * D + 1) ≤
      (n + 1) * (2 * D + 1) := max_le hlevel (by nlinarith)
  have hD : (2 * D + 1).size ≤ D.size + 2 := by
    apply Nat.size_le.mpr
    have hd := Nat.lt_size_self D
    rw [show D.size + 2 = D.size + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  have hs := (Nat.size_le_size hmax).trans (size_mul_le (n + 1) (2 * D + 1))
  unfold width
  have hn := size_le_self (n + 1)
  omega

/-- Logarithm of the explicit upper bound on Macaulay columns. -/
def columnExponent (n D : ℕ) : ℕ := (n + 1) * width n D

/-- Coefficient budget exponent from a mass allowance `mass q ≤ 2^b`. -/
def budgetExponent (D b : ℕ) : ℕ := D.size + 2 * b + 3

/-- A radius exponent calculated entirely from source allowances. -/
def massExponent (n D b : ℕ) : ℕ :=
  columnBound n D * (columnExponent n D + budgetExponent D b) + 1

theorem columnBound_eq (n D : ℕ) : columnBound n D = 2 ^ columnExponent n D := by
  simp only [columnBound, FixedWidthPolynomial.count, columnExponent, ← pow_mul, Nat.mul_comm]

theorem coefficientBudget_le {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hb : MvMass.mass q ≤ 2 ^ b) : CoerciveCriticalBounds.coefficientBudget q D ≤ 2 ^ budgetExponent D b := by
  have hD : 2 * D + 2 ≤ 2 ^ (D.size + 2) := by
    have hd := Nat.lt_size_self D
    rw [show D.size + 2 = D.size + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  have hq : MvMass.mass q ^ 2 + 1 ≤ 2 ^ (2 * b + 1) := by
    have hm : MvMass.mass q ^ 2 ≤ (2 ^ b) ^ 2 := Nat.pow_le_pow_left hb 2
    have hp : 1 ≤ 2 ^ (2 * b) := Nat.one_le_pow _ _ (by decide)
    rw [← pow_mul, Nat.mul_comm b 2] at hm
    calc
      _ ≤ 2 ^ (2 * b) + 1 := Nat.add_le_add_right hm 1
      _ ≤ 2 ^ (2 * b) * 2 := by omega
      _ = _ := (pow_succ 2 (2 * b)).symm
  unfold CoerciveCriticalBounds.coefficientBudget
  calc
    _ ≤ 2 ^ (D.size + 2) * 2 ^ (2 * b + 1) := Nat.mul_le_mul hD hq
    _ = _ := by rw [← pow_add]; congr 1; unfold budgetExponent; omega

/-- The actual determinant mass bound fits below a power of two whose
exponent is calculated without reading the exact polynomial mass. -/
theorem massBound_add_one_le {n : ℕ} (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hb : MvMass.mass q ≤ 2 ^ b) : massBound q D + 1 ≤ 2 ^ massExponent n D b := by
  let C := columnBound n D
  let L := columnExponent n D
  let K := budgetExponent D b
  have hfac : C.factorial ≤ (2 ^ L) ^ C := (Nat.factorial_le_pow C).trans
    (Nat.pow_le_pow_left (by exact (columnBound_eq n D).le) C)
  have hbudget := Nat.pow_le_pow_left (coefficientBudget_le q D b hb) C
  have hm : massBound q D ≤ 2 ^ (C * (L + K)) := by
    calc
      _ ≤ (2 ^ L) ^ C * (2 ^ K) ^ C := Nat.mul_le_mul hfac hbudget
      _ = _ := by rw [← mul_pow, ← pow_add, ← pow_mul, Nat.mul_comm (L + K) C]
  have hp : 1 ≤ 2 ^ (C * (L + K)) := Nat.one_le_pow _ _ (by decide)
  change massBound q D + 1 ≤ 2 ^ (C * (L + K) + 1)
  rw [pow_succ]
  omega

/-- The exponent has polynomial binary length in dimension, degree length,
and the binary length of the coefficient-mass allowance exponent. -/
theorem massExponent_size_le (n D b : ℕ) :
    (massExponent n D b).size ≤ 8 * (n + D.size + b.size + 4) ^ 2 := by
  have hK : (budgetExponent D b).size ≤ D.size + b.size + 7 := by
    have h1 := size_add_le (D.size + 2 * b) 3
    have h2 := size_add_le D.size (2 * b)
    have h3 := size_mul_le 2 b
    have h4 := size_le_self D.size
    have ht : (3 : ℕ).size = 2 := by decide
    have ht2 : (2 : ℕ).size = 2 := by decide
    rw [ht] at h1
    rw [ht2] at h3
    unfold budgetExponent
    omega
  have hC : (columnBound n D).size = columnExponent n D + 1 := by rw [columnBound_eq, Nat.size_pow]
  have hs1 := size_add_le
    (columnBound n D * (columnExponent n D + budgetExponent D b)) 1
  have hs2 := size_mul_le (columnBound n D) (columnExponent n D + budgetExponent D b)
  have hs3 := size_add_le (columnExponent n D) (budgetExponent D b)
  have hs4 := size_le_self (columnExponent n D)
  have hL : columnExponent n D ≤ (n + 1) * (n + D.size + 3) :=
    Nat.mul_le_mul_left (n + 1) (width_le n D)
  have hsize : (massExponent n D b).size ≤ 2 * columnExponent n D + D.size + b.size + 11 := by
    unfold massExponent
    norm_num at hs1
    omega
  exact hsize.trans (by nlinarith [sq_nonneg (n : ℤ)])

/-- Exponent bounding the diagonal penalty on the radius box. -/
def penaltyExponent (n D b : ℕ) : ℕ := massExponent n D b * (2 * D + 2) + n.size

theorem penaltyExponent_size_le (n D b : ℕ) :
    (penaltyExponent n D b).size ≤ 16 * (n + D.size + b.size + 4) ^ 2 := by
  have hN : (2 * D + 2).size ≤ D.size + 2 := by
    apply Nat.size_le.mpr
    have hd := Nat.lt_size_self D
    rw [show D.size + 2 = D.size + 1 + 1 by omega, pow_succ, pow_succ]
    omega
  have h1 := size_add_le (massExponent n D b * (2 * D + 2)) n.size
  have h2 := size_mul_le (massExponent n D b) (2 * D + 2)
  have h3 := size_le_self n.size
  have h4 := size_le_self n
  have he := massExponent_size_le n D b
  have hs : n + D.size + b.size + 4 ≤ (n + D.size + b.size + 4) ^ 2 :=
    le_self_pow₀ (by omega) (by decide)
  unfold penaltyExponent
  omega

/-- An entirely implicit power-of-two bound on the penalty of every point in
the coordinate radius box. No large radius polynomial is constructed. -/
theorem penalty_le (n D b : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, |x i| ≤ (2 : ℝ) ^ massExponent n D b) :
    (∑ i, x i ^ (2 * D + 2)) ≤ (2 : ℝ) ^ penaltyExponent n D b := by
  have hcoord (i : Fin n) : x i ^ (2 * D + 2) ≤
      ((2 : ℝ) ^ massExponent n D b) ^ (2 * D + 2) := by
    calc
      _ ≤ |x i ^ (2 * D + 2)| := le_abs_self _
      _ = |x i| ^ (2 * D + 2) := abs_pow _ _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hx i) _
  have hn : (n : ℝ) ≤ (2 : ℝ) ^ n.size := by
    exact_mod_cast (Nat.lt_size_self n).le
  calc
    _ ≤ ∑ _i : Fin n, ((2 : ℝ) ^ massExponent n D b) ^ (2 * D + 2) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (n : ℝ) * ((2 : ℝ) ^ massExponent n D b) ^ (2 * D + 2) := by simp
    _ ≤ (2 : ℝ) ^ n.size * ((2 : ℝ) ^ massExponent n D b) ^ (2 * D + 2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; unfold penaltyExponent; omega

end LeanCanny.Algebra.CoerciveRadiusBits

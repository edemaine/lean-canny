/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerPSPACE
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Binomial coefficients as streamed power entries

The lower bidiagonal matrix with diagonal and subdiagonal entries one has
`choose n (i-j)` in its nth power below the diagonal. Thus one binomial
coefficient is a selected power entry in dimension `k+1`; no Pascal row or
intermediate integer binomial coefficient needs to be stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.BinomialPower

variable {R : Type*} [Semiring R]

def matrix (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) R := fun i j =>
  (if j = i then 1 else 0) + (if i.val = j.val + 1 then 1 else 0)

theorem matrix_zero (d : ℕ) (j : Fin (d + 1)) :
    matrix (R := R) d 0 j = if j = 0 then 1 else 0 := by
  have hn : ¬ (0 : ℕ) = j.val + 1 := by omega
  simp only [matrix, Fin.val_zero, hn, ↓reduceIte, add_zero]

theorem matrix_succ (d : ℕ) (i : Fin d) (j : Fin (d + 1)) :
    matrix (R := R) d i.succ j =
      (if j = i.succ then 1 else 0) + (if j = i.castSucc then 1 else 0) := by
  have he : (i.succ.val = j.val + 1) = (j = i.castSucc) := by
    apply propext
    rw [Fin.ext_iff]
    change (i.val + 1 = j.val + 1) ↔ j.val = i.val
    omega
  simp only [matrix, he]

theorem mul_zero (d : ℕ) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) R) (j : Fin (d + 1)) :
    (matrix (R := R) d * B) 0 j = B 0 j := by
  simp [Matrix.mul_apply, matrix_zero, ite_mul]

theorem mul_succ (d : ℕ) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) R)
    (i : Fin d) (j : Fin (d + 1)) :
    (matrix (R := R) d * B) i.succ j = B i.succ j + B i.castSucc j := by
  simp [Matrix.mul_apply, matrix_succ, add_mul, ite_mul, Finset.sum_add_distrib]

theorem pow_apply (d n : ℕ) (i j : Fin (d + 1)) :
    (matrix (R := R) d ^ n) i j =
      if j.val ≤ i.val then (n.choose (i.val - j.val) : R) else 0 := by
  induction n generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases he : i = j
    · subst j
      simp
    · by_cases hj : j.val ≤ i.val
      · have hne : i.val - j.val ≠ 0 := by
          have hv : i.val ≠ j.val := by simpa only [Fin.ext_iff] using he
          omega
        cases hdiff : i.val - j.val with
        | zero => exact False.elim (hne hdiff)
        | succ k => simp [he, hj]
      · simp [he, hj]
  | succ n ih =>
    rw [pow_succ']
    induction i using Fin.cases with
    | zero =>
      rw [mul_zero, ih]
      by_cases hj : j = 0
      · simp [hj]
      · have hv : ¬ j.val ≤ 0 := by
          have hne : j.val ≠ 0 := by simpa only [Fin.ext_iff, Fin.val_zero] using hj
          omega
        simp [hv]
    | succ i =>
      rw [mul_succ, ih, ih]
      simp only [Fin.val_succ, Fin.val_castSucc]
      by_cases hj : j.val ≤ i.val
      · have hs : j.val ≤ i.val + 1 := by omega
        have hd : i.val + 1 - j.val = (i.val - j.val) + 1 := by omega
        simp only [hj, hs, ↓reduceIte, hd]
        rw [Nat.choose_succ_succ, Nat.cast_add]
        exact add_comm _ _
      · by_cases he : j.val = i.val + 1
        · simp [he]
        · have hs : ¬ j.val ≤ i.val + 1 := by omega
          simp [hj, hs]

theorem pow_last_zero (n k : ℕ) :
    (matrix (R := R) k ^ n) (Fin.last k) 0 = (n.choose k : R) := by
  simp only [pow_apply, Fin.val_zero, Fin.val_last, Nat.zero_le, ↓reduceIte, Nat.sub_zero]

theorem matrix_apply (d : ℕ) (i j : Fin (d + 1)) :
    matrix (R := R) d i j = if i.val = j.val ∨ i.val = j.val + 1 then 1 else 0 := by
  simp only [matrix]
  by_cases hd : i = j
  · have hn : ¬ i.val = j.val + 1 := by simp only [hd]; omega
    simp [hd]
  · have hv : i.val ≠ j.val := by simpa only [Fin.ext_iff] using hd
    simp only [Ne.symm hd, ↓reduceIte, zero_add, hv, false_or]

end LeanCanny.Algebra.BinomialPower

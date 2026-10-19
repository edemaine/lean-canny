/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Subresultant
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# The common-root relation between the first two subresultant minors

A bounded-degree family of columns vanishing at `b` makes its constant row a
linear combination of the positive-degree rows. Replacing the first row of
the high-coefficient matrix multiplies its determinant by `-b`. This gives
the ratio identity needed for the first subresultant. For degree bounds `m,n>1`,
the first subresultant is its linear coefficient times `X-b`. Over a field the
root is the negative coefficient ratio when the denominator is nonzero.
Nonvanishing from a linear GCD is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.Subresultant
open Polynomial
open scoped BigOperators

def highMatrix {R : Type*} [Semiring R] {s : ℕ} (Q : Fin s → Polynomial R) : Matrix (Fin s) (Fin s) R :=
  fun i j => (Q j).coeff (i.val + 1)

theorem constant_row_eq {R : Type*} [CommRing R] {s : ℕ} (Q : Fin s → Polynomial R) (b : R)
    (hdegree : ∀ j, (Q j).natDegree ≤ s) (hroot : ∀ j, (Q j).eval b = 0) :
    (fun j => (Q j).coeff 0) = ∑ i : Fin s, (-(b ^ (i.val + 1))) • highMatrix Q i := by
  funext j
  have he := Polynomial.eval_eq_sum_range' (p := Q j) (n := s + 1) (by have := hdegree j; omega) b
  rw [hroot j, Finset.sum_range_succ'] at he
  simp only [pow_zero, mul_one] at he
  have hs : (∑ i : Fin s, b ^ (i.val + 1) * (Q j).coeff (i.val + 1)) =
      ∑ i ∈ Finset.range s, (Q j).coeff (i + 1) * b ^ (i + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => b ^ (i + 1) * (Q j).coeff (i + 1)) s]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, highMatrix, neg_mul, Finset.sum_neg_distrib]
  rw [hs]
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using he.symm)

theorem constant_row_det {R : Type*} [CommRing R] {s : ℕ} (Q : Fin s → Polynomial R) (b : R)
    (hs : 0 < s) (hdegree : ∀ j, (Q j).natDegree ≤ s) (hroot : ∀ j, (Q j).eval b = 0) :
    ((highMatrix Q).updateRow ⟨0, hs⟩ (fun j => (Q j).coeff 0)).det = -b * (highMatrix Q).det := by
  rw [constant_row_eq Q b hdegree hroot, Matrix.det_updateRow_sum]
  simp only [Nat.zero_add, pow_one, smul_eq_mul]

theorem band_eq_coeff_mul_X_pow {R : Type*} [Semiring R] (f : Polynomial R) (d i j : ℕ)
    (hf : f.natDegree ≤ d) : band f d i j = (f * X ^ j).coeff i := by
  rw [Polynomial.coeff_mul_X_pow']
  unfold band
  by_cases hj : j ≤ i
  · rw [ite_eq_left hj]
    by_cases hi : i ≤ j + d
    · rw [ite_eq_left ⟨hj, hi⟩]
    · rw [ite_eq_right (by omega : ¬ (j ≤ i ∧ i ≤ j + d)), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  · rw [ite_eq_right hj, ite_eq_right (by omega : ¬ (j ≤ i ∧ i ≤ j + d))]

noncomputable def shiftedColumns {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ) :
    Fin ((m - 1) + (n - 1)) → Polynomial R :=
  fun j => j.addCases (fun j => g * X ^ j.val) (fun j => f * X ^ j.val)

theorem shiftedColumns_degree {R : Type*} [Semiring R] [Nontrivial R] (f g : Polynomial R) (m n : ℕ)
    (hm : 1 < m) (hn : 1 < n) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (j : Fin ((m - 1) + (n - 1))) : (shiftedColumns f g m n j).natDegree ≤ (m - 1) + (n - 1) := by
  induction j using Fin.addCases with
  | left j =>
    have h : (g * X ^ j.val).natDegree ≤ g.natDegree + (X ^ j.val : Polynomial R).natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X_pow] at h
    have hj := j.is_lt
    simpa only [shiftedColumns, Fin.addCases_left] using (show (g * X ^ j.val).natDegree ≤ (m - 1) + (n - 1) by omega)
  | right j =>
    have h : (f * X ^ j.val).natDegree ≤ f.natDegree + (X ^ j.val : Polynomial R).natDegree := Polynomial.natDegree_mul_le
    simp only [Polynomial.natDegree_X_pow] at h
    have hj := j.is_lt
    simpa only [shiftedColumns, Fin.addCases_right] using (show (f * X ^ j.val).natDegree ≤ (m - 1) + (n - 1) by omega)

theorem shiftedColumns_eval {R : Type*} [CommSemiring R] (f g : Polynomial R) (m n : ℕ) (b : R)
    (hf : f.eval b = 0) (hg : g.eval b = 0) (j : Fin ((m - 1) + (n - 1))) :
    (shiftedColumns f g m n j).eval b = 0 := by
  induction j using Fin.addCases <;> simp only [shiftedColumns, Fin.addCases_left, Fin.addCases_right,
    Polynomial.eval_mul, hf, hg, zero_mul]

theorem minor_first_apply {R : Type*} [Semiring R] (f g : Polynomial R) (m n r : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (i j : Fin ((m - 1) + (n - 1))) :
    minor f g m n 1 r i j = (shiftedColumns f g m n j).coeff (rowIndex 1 r i.val) := by
  induction j using Fin.addCases <;>
    simp only [minor, Matrix.of_apply, shiftedColumns, Fin.addCases_left, Fin.addCases_right,
      band_eq_coeff_mul_X_pow _ _ _ _ hf, band_eq_coeff_mul_X_pow _ _ _ _ hg]

theorem rowIndex_one (i : ℕ) : rowIndex 1 1 i = i + 1 := by
  by_cases h : i = 0 <;> simp [rowIndex, h, Nat.add_comm]

theorem minor_first_one {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    minor f g m n 1 1 = highMatrix (shiftedColumns f g m n) := by
  funext i j
  rw [minor_first_apply f g m n 1 hf hg, rowIndex_one]
  rfl

theorem minor_first_zero {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hs : 0 < (m - 1) + (n - 1)) :
    minor f g m n 1 0 = (highMatrix (shiftedColumns f g m n)).updateRow ⟨0, hs⟩
      (fun j => (shiftedColumns f g m n j).coeff 0) := by
  funext i j
  rw [minor_first_apply f g m n 0 hf hg]
  by_cases hi : i.val = 0
  · have hi' : i = ⟨0, hs⟩ := Fin.ext hi
    subst i
    rw [Matrix.updateRow_self]
    rfl
  · have hi' : i ≠ ⟨0, hs⟩ := fun h => hi (congrArg Fin.val h)
    rw [Matrix.updateRow_ne hi']
    simp only [rowIndex, hi, ↓reduceIte, highMatrix, Nat.add_comm]

theorem first_constant_eq_neg_mul {R : Type*} [CommRing R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (b : R)
    (hm : 1 < m) (hn : 1 < n) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hfb : f.eval b = 0) (hgb : g.eval b = 0) :
    (minor f g m n 1 0).det = -b * (minor f g m n 1 1).det := by
  rw [minor_first_zero f g m n hf hg (by omega), minor_first_one f g m n hf hg]
  exact constant_row_det _ b (by omega) (shiftedColumns_degree f g m n hm hn hf hg)
    (shiftedColumns_eval f g m n b hfb hgb)

theorem first_eq_mul_X_sub_C {R : Type*} [CommRing R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (b : R)
    (hm : 1 < m) (hn : 1 < n) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hfb : f.eval b = 0) (hgb : g.eval b = 0) :
    polynomial f g m n 1 = C (minor f g m n 1 1).det * (X - C b) := by
  rw [first_eq_linear f g m n hm hn, first_constant_eq_neg_mul f g m n b hm hn hf hg hfb hgb,
    map_mul, map_neg]
  ring

theorem first_eval_eq_zero {R : Type*} [CommRing R] [Nontrivial R]
    (f g : Polynomial R) (m n : ℕ) (b : R)
    (hm : 1 < m) (hn : 1 < n) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hfb : f.eval b = 0) (hgb : g.eval b = 0) :
    (polynomial f g m n 1).eval b = 0 := by
  rw [first_eq_mul_X_sub_C f g m n b hm hn hf hg hfb hgb]
  simp

theorem root_eq_neg_div {K : Type*} [Field K] (f g : Polynomial K) (m n : ℕ) (b : K)
    (hm : 1 < m) (hn : 1 < n) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n)
    (hfb : f.eval b = 0) (hgb : g.eval b = 0) (hden : (minor f g m n 1 1).det ≠ 0) :
    b = -(minor f g m n 1 0).det / (minor f g m n 1 1).det := by
  rw [eq_div_iff hden, first_constant_eq_neg_mul f g m n b hm hn hf hg hfb hgb]
  ring

end LeanCanny.Algebra.Subresultant

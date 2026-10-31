/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CharacteristicCoefficientDegree

/-! # Retained parameter degrees in matrix powers and characteristic polynomials

Every matrix product adds the entry degree bounds. Each characteristic
coefficient has degree at most the dimension times the entry bound. These
estimates hold over arbitrary commutative coefficient rings.
-/

@[expose] public section
namespace LeanCanny.Algebra.RelativeMatrixDegree
open scoped Classical BigOperators
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def Bound (A : Matrix ι ι (Polynomial R)) (E : ℕ) : Prop := ∀ i j, (A i j).natDegree ≤ E

omit [Fintype ι] in
theorem one : Bound (1 : Matrix ι ι (Polynomial R)) 0 := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem mul {A B : Matrix ι ι (Polynomial R)} {E F : ℕ} (hA : Bound A E) (hB : Bound B F) :
    Bound (A * B) (E + F) := by
  intro i j
  rw [Matrix.mul_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA i k) (hB k j))

theorem pow {A : Matrix ι ι (Polynomial R)} {E : ℕ} (hA : Bound A E) (k : ℕ) :
    Bound (A ^ k) (k * E) := by
  induction k with
  | zero => simpa only [pow_zero, Nat.zero_mul] using one (ι := ι) (R := R)
  | succ k ih => simpa only [pow_succ, Nat.succ_mul] using mul ih hA

theorem charpoly_coefficient {A : Matrix ι ι (Polynomial R)} {E : ℕ} (hA : Bound A E) (k : ℕ) :
    (A.charpoly.coeff k).natDegree ≤ Fintype.card ι * E := by
  have HC : ∀ i j t, ((A.charmatrix i j).coeff t).natDegree ≤ E := by
    intro i j t
    by_cases hij : i = j
    · subst j
      rw [Matrix.charmatrix_apply_eq]
      cases t with
      | zero => simpa using hA i i
      | succ t =>
        cases t with
        | zero => simp
        | succ t => simp [Polynomial.coeff_X]
    · rw [Matrix.charmatrix_apply_ne A i j hij]
      cases t with
      | zero => simpa using hA i j
      | succ t => simp
  have H := PolynomialKronecker.determinant_inner_degree A.charmatrix (fun _ => E) HC k
  simpa only [Matrix.charpoly, Finset.sum_const, Finset.card_univ, smul_eq_mul] using H

end LeanCanny.Algebra.RelativeMatrixDegree

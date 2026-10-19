/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitiveResultant
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Size

/-!
# Direct access to the coefficients of the shifted polynomial family

The coefficient of `x^i θ^j` in `p(θ-c*x)` is a binomial coefficient times one
input coefficient times `(-c)^i`. This formula is valid over any commutative
ring, including the integers. It permits accessing Sylvester-matrix entries
without first expanding and storing the complete bivariate polynomial.
It is an algebraic identity; encoded arithmetic and its space bounds are separate.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

variable {R : Type*} [CommRing R]

theorem shiftFamily_eq_taylor (p : Polynomial R) (c : ℕ) :
    shiftFamily p c = (Polynomial.taylor X (p.map C)).comp (C (C (-(c : R))) * X) := by
  rw [shiftFamily, Polynomial.taylor_apply, Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, map_neg]
  ring

theorem shiftFamily_coeff (p : Polynomial R) (c i : ℕ) :
    (shiftFamily p c).coeff i = Polynomial.hasseDeriv i p * C (-(c : R)) ^ i := by
  rw [shiftFamily_eq_taylor, Polynomial.comp_C_mul_X_coeff, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_map]
  congr 1
  rw [Polynomial.eval_map]
  change Polynomial.aeval (X : Polynomial R) (Polynomial.hasseDeriv i p) = _
  exact Polynomial.aeval_X_left_apply _

theorem shiftFamily_coeff_natDegree_le (p : Polynomial R) (c i : ℕ) :
    ((shiftFamily p c).coeff i).natDegree ≤ p.natDegree - i := by
  rw [shiftFamily_coeff, ← map_pow]
  exact (Polynomial.natDegree_mul_C_le _ _).trans
    (Polynomial.natDegree_hasseDeriv_le p i)

/-- One coefficient requires only one input coefficient, a binomial coefficient,
and a power. No sum over the remaining coefficients occurs. -/
theorem shiftFamily_coeff_coeff (p : Polynomial R) (c i j : ℕ) :
    ((shiftFamily p c).coeff i).coeff j =
      ((i + j).choose i : R) * p.coeff (i + j) * (-(c : R)) ^ i := by
  rw [shiftFamily_coeff, ← map_pow, Polynomial.coeff_mul_C, Polynomial.hasseDeriv_coeff]
  simp only [Nat.add_comm]

theorem shiftFamily_coeff_natAbs (p : Polynomial ℤ) (c i j : ℕ) :
    (((shiftFamily p c).coeff i).coeff j).natAbs =
      (i + j).choose i * (p.coeff (i + j)).natAbs * c ^ i := by
  rw [shiftFamily_coeff_coeff]
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_natCast]

/-- A uniform integer coefficient bound, including indices outside the support. -/
theorem shiftFamily_coeff_natAbs_le (p : Polynomial ℤ) (c H i j : ℕ)
    (hH : ∀ k, (p.coeff k).natAbs ≤ H) :
    (((shiftFamily p c).coeff i).coeff j).natAbs ≤
      2 ^ p.natDegree * H * (c + 1) ^ p.natDegree := by
  rw [shiftFamily_coeff_natAbs]
  by_cases hij : i + j ≤ p.natDegree
  · have hchoose := (Nat.choose_le_two_pow (i + j) i).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hij)
    have hpower : c ^ i ≤ (c + 1) ^ p.natDegree :=
      (Nat.pow_le_pow_left (Nat.le_succ c) i).trans
        (Nat.pow_le_pow_right (by omega : 0 < c + 1) (by omega : i ≤ p.natDegree))
    exact Nat.mul_le_mul (Nat.mul_le_mul hchoose (hH (i + j))) hpower
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i + j)]
    simp

/-- Bit length grows linearly in the degree and input coefficient length,
and logarithmically in the chosen integer direction. -/
theorem shiftFamily_coeff_size_le (p : Polynomial ℤ) (c H i j : ℕ)
    (hH : ∀ k, (p.coeff k).natAbs ≤ H) :
    (((shiftFamily p c).coeff i).coeff j).natAbs.size ≤
      p.natDegree + H.size + (c + 1).size * p.natDegree + 1 := by
  have hs := shiftFamily_coeff_natAbs_le p c H i j hH
  have hm := Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ p.natDegree) (Nat.lt_size_self H).le)
    (Nat.pow_le_pow_left (Nat.lt_size_self (c + 1)).le p.natDegree)
  have he : 2 ^ p.natDegree * 2 ^ H.size * (2 ^ (c + 1).size) ^ p.natDegree =
      2 ^ (p.natDegree + H.size + (c + 1).size * p.natDegree) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
  have hbound := hs.trans (hm.trans_eq he)
  simpa only [Nat.size_pow] using Nat.size_le_size hbound

end LeanCanny.Algebra

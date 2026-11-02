/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ClearedDilatedCoordinatePolynomial
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Integer matrix coefficients for denominator-cleared limit coordinates

The extra denominator is an integer scalar. Its matrix operation is scalar
multiplication, so the old critical coefficient and one denominator residue
suffice even over a retained algebra with zero divisors.
-/
@[expose] public section
namespace LeanCanny.Algebra.ClearedDilatedCoordinateMatrix
open Polynomial
variable {A I : Type*} [CommRing A] [Fintype I] [DecidableEq I]

theorem coefficient (b : Module.Basis I ℤ A) (p : Polynomial (Polynomial A))
    (q : ℤ) (c k : ℕ) :
    Algebra.leftMulMatrix b
      (((Bivariate.swap (ClearedDilatedCoordinatePolynomial.rescale p (q : A))).coeff c).coeff k) =
      if k ≤ c then q ^ (p.natDegree-k) • Algebra.leftMulMatrix b ((p.coeff k).coeff (c-k)) else 0 := by
  rw [ClearedDilatedCoordinatePolynomial.swapped_coefficient]
  split_ifs
  · rw [← Int.cast_pow, mul_comm, ← zsmul_eq_mul]
    exact map_zsmul (Algebra.leftMulMatrix b) _ _
  · exact map_zero _

theorem entry_bound (b : Module.Basis I ℤ A) (p : Polynomial (Polynomial A))
    (q : ℤ) (H L : ℕ)
    (hp : ∀ k j i t, ((Algebra.leftMulMatrix b ((p.coeff k).coeff j)) i t).natAbs ≤ 2 ^ H)
    (hq : q.natAbs ≤ 2 ^ L) (c k : ℕ) (i t : I) :
    ((Algebra.leftMulMatrix b
      (((Bivariate.swap (ClearedDilatedCoordinatePolynomial.rescale p (q : A))).coeff c).coeff k)) i t).natAbs ≤
      2 ^ (H + p.natDegree * L) := by
  rw [coefficient]
  split_ifs
  · simp only [Matrix.smul_apply, smul_eq_mul, Int.natAbs_mul, Int.natAbs_pow]
    calc
      _ ≤ (2 ^ L) ^ (p.natDegree-k) * 2 ^ H := by gcongr; exact hp k (c-k) i t
      _ = 2 ^ (H + (p.natDegree-k) * L) := by
        rw [← pow_mul, ← pow_add, Nat.mul_comm L, Nat.add_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
        (Nat.mul_le_mul_right L (Nat.sub_le p.natDegree k)) H)
  · simp only [Matrix.zero_apply, Int.natAbs_zero, Nat.zero_le]

end LeanCanny.Algebra.ClearedDilatedCoordinateMatrix

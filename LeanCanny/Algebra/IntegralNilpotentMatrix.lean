/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralNilpotentParameter

/-! # Exact triangular multiplication matrices in a formal nilpotent

Every entry reads the original coefficient at the difference of the two
nilpotent digits. A column digit above the row digit gives zero. This
holds for arbitrary polynomials; high terms disappear in the quotient
without wrapping into lower digits.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralNilpotentMatrix
open Polynomial IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
variable {A : Type*} [CommRing A] [Nontrivial A]

omit [Nontrivial A] in
theorem remainder_coefficient (N : ℕ) (f : Polynomial A) (k : ℕ) (hk : k < N) :
    (f %ₘ (X ^ N)).coeff k = f.coeff k := by
  have H := congrArg (fun p : Polynomial A => p.coeff k) (Polynomial.modByMonic_add_div f (X ^ N))
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', ite_eq_right (Nat.not_le_of_lt hk), add_zero] at H
  exact H

theorem relative (N : ℕ) (f : Polynomial A) (e h : Fin N) :
    Algebra.leftMulMatrix (relativeBasis (X ^ N) (monic_X_pow N) (natDegree_X_pow N))
      (AdjoinRoot.mk (X ^ N) f) e h = if h.val ≤ e.val then f.coeff (e.val - h.val) else 0 := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, relativeBasis_apply,
    ← AdjoinRoot.mk_X, ← map_pow, ← map_mul, relativeBasis_repr,
    remainder_coefficient N (f * X ^ h.val) e.val e.isLt, Polynomial.coeff_mul_X_pow']

theorem tower {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ A)
    (N : ℕ) (f : Polynomial A) (r t : ι) (e h : Fin N) :
    Algebra.leftMulMatrix (b.smulTower (relativeBasis (X ^ N) (monic_X_pow N) (natDegree_X_pow N)))
      (AdjoinRoot.mk (X ^ N) f) (r, e) (t, h) =
        if h.val ≤ e.val then Algebra.leftMulMatrix b (f.coeff (e.val - h.val)) r t else 0 := by
  rw [Algebra.smulTower_leftMulMatrix, relative]
  split_ifs <;> simp only [map_zero, Matrix.zero_apply]

theorem fixedWidth {m B : ℕ} (b : IntegralCoordinateBasis A m (2 ^ B))
    (f : Polynomial A) (r t : Fin (count m B)) (e h : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (b.step (X ^ (2 ^ B)) (monic_X_pow _) (natDegree_X_pow _)).finBasis
      (AdjoinRoot.mk (X ^ (2 ^ B)) f) (pairIndex m B (r, e)) (pairIndex m B (t, h)) =
        if h.val ≤ e.val then Algebra.leftMulMatrix b.finBasis (f.coeff (e.val - h.val)) r t else 0 := by
  rw [finBasis_step_matrix]
  exact tower b.finBasis (2 ^ B) f r t e h

end LeanCanny.Algebra.IntegralNilpotentMatrix

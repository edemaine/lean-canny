/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasisFinStep
public import LeanCanny.Algebra.PaddedIntegralNormalization
public import Mathlib.Basic.Real.Basic

/-! # A formal nilpotent scalar and exact coefficient extraction

A pure-power integer birth pads to the same pure power. Its real scalar
value is zero, but its prefix generator retains all formal coefficients
below the fixed cap. Multiplication-matrix entries from scalar digit zero
to digit e recover the old coefficient matrix exactly.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralNilpotentParameter
open Polynomial IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
variable {A : Type*} [CommRing A] [Nontrivial A]

omit [Nontrivial A] in
theorem purePower_normalization (c : A) (d N : ℕ) (hd : d ≤ N) :
    PaddedIntegralNormalization.polynomial (monomial d c) d N = X ^ N := by
  have HE : FixedDegreeIntegralNormalization.polynomial (monomial d c) d = X ^ d := by
    ext k
    rw [FixedDegreeIntegralNormalization.coefficient, coeff_X_pow]
    have H (hk : k < d) : (monomial d c).coeff k = 0 := by
      rw [coeff_monomial, ite_eq_right (by omega)]
    by_cases hk : k < d
    · rw [ite_eq_left hk, H hk, zero_mul, add_zero]
    · rw [ite_eq_right hk, add_zero]
  rw [PaddedIntegralNormalization.polynomial, ite_eq_left hd, HE, ← pow_add, Nat.sub_add_cancel hd]

omit [Nontrivial A] in
theorem root_nilpotent (N : ℕ) : (AdjoinRoot.root (X ^ N : Polynomial A)) ^ N = 0 := by
  rw [← AdjoinRoot.mk_X, ← map_pow]
  exact AdjoinRoot.mk_self

omit [Nontrivial A] in
theorem real_value_zero (N : ℕ) (φ : AdjoinRoot (X ^ N : Polynomial A) →+* ℝ) :
    φ (AdjoinRoot.root _) = 0 := by
  apply eq_zero_of_pow_eq_zero (n := N)
  rw [← map_pow, root_nilpotent, map_zero]

theorem relative_coefficient (N : ℕ) (f : Polynomial A) (hf : f.natDegree < N) (e : Fin N) :
    Algebra.leftMulMatrix (relativeBasis (X ^ N) (monic_X_pow N) (natDegree_X_pow N))
      (AdjoinRoot.mk (X ^ N) f) e ⟨0, by have H := e.isLt; omega⟩ = f.coeff e.val := by
  rw [Algebra.leftMulMatrix_eq_repr_mul, relativeBasis_apply, pow_zero, mul_one, relativeBasis_repr]
  rw [(modByMonic_eq_self_iff (monic_X_pow N)).mpr]
  rw [degree_X_pow]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hf)

theorem tower_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ A) (N : ℕ) (f : Polynomial A) (hf : f.natDegree < N)
    (r t : ι) (e : Fin N) :
    Algebra.leftMulMatrix (b.smulTower (relativeBasis (X ^ N) (monic_X_pow N) (natDegree_X_pow N)))
      (AdjoinRoot.mk (X ^ N) f) (r, e) (t, ⟨0, by have H := e.isLt; omega⟩) =
        Algebra.leftMulMatrix b (f.coeff e.val) r t := by
  rw [Algebra.smulTower_leftMulMatrix, relative_coefficient N f hf e]

theorem fixedWidth_coefficient {m B : ℕ} (b : IntegralCoordinateBasis A m (2 ^ B))
    (f : Polynomial A) (hf : f.natDegree < 2 ^ B) (r t : Fin (count m B)) (e : Fin (2 ^ B)) :
    Algebra.leftMulMatrix (b.step (X ^ (2 ^ B)) (monic_X_pow _) (natDegree_X_pow _)).finBasis
      (AdjoinRoot.mk (X ^ (2 ^ B)) f) (pairIndex m B (r, e)) (pairIndex m B (t, 0)) =
        Algebra.leftMulMatrix b.finBasis (f.coeff e.val) r t := by
  rw [finBasis_step_matrix]
  exact tower_coefficient b.finBasis (2 ^ B) f hf r t e

end LeanCanny.Algebra.IntegralNilpotentParameter

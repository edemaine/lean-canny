/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralNilpotentParameter
public import LeanCanny.Algebra.RelativeMatrixDegree

/-! # Characteristic coefficients through a bounded nilpotent parameter

An auxiliary-polynomial matrix can be evaluated at a formal nilpotent
without losing any characteristic coefficient when the cap exceeds the
matrix dimension times the entry degree. The coefficient is recovered
as an actual integral multiplication-matrix entry over the older prefix.
The degree bound uses the relative matrix dimension, not the old prefix rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralNilpotentCharacteristic
open Polynomial IntegralCoordinateBasis
open scoped Classical
variable {A σ ι : Type*} [CommRing A] [Nontrivial A]
variable [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]

theorem coefficient (b : Module.Basis ι ℤ A) (M : Matrix σ σ (Polynomial A))
    (E N : ℕ) (hM : RelativeMatrixDegree.Bound M E) (hN : Fintype.card σ * E < N)
    (k : ℕ) (e : Fin N) (r t : ι) :
    Algebra.leftMulMatrix
      (b.smulTower (relativeBasis (X ^ N) (monic_X_pow N) (natDegree_X_pow N)))
      ((M.map (AdjoinRoot.mk (X ^ N))).charpoly.coeff k)
      (r, e) (t, ⟨0, by have H := e.isLt; omega⟩) =
        Algebra.leftMulMatrix b ((M.charpoly.coeff k).coeff e.val) r t := by
  rw [Matrix.charpoly_map, Polynomial.coeff_map]
  exact IntegralNilpotentParameter.tower_coefficient b N (M.charpoly.coeff k)
    ((RelativeMatrixDegree.charpoly_coefficient hM k).trans_lt hN) r t e

omit [Nontrivial A] in
theorem scalar_degree (M : Matrix σ σ (Polynomial A)) (N : ℕ) :
    (M.map (AdjoinRoot.mk (X ^ N))).charpoly.natDegree ≤ Fintype.card σ := by
  by_cases H : Nontrivial (AdjoinRoot (X ^ N : Polynomial A))
  · let _ := H
    exact (Matrix.charpoly_natDegree_eq_dim _).le
  · have : Subsingleton (AdjoinRoot (X ^ N : Polynomial A)) := not_nontrivial_iff_subsingleton.mp H
    have HE : (M.map (AdjoinRoot.mk (X ^ N))).charpoly = 0 := Subsingleton.elim _ _
    rw [HE, Polynomial.natDegree_zero]
    exact Nat.zero_le _

end LeanCanny.Algebra.IntegralNilpotentCharacteristic

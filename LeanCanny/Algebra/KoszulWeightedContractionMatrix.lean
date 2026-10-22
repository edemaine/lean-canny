/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedContraction
public import LeanCanny.Algebra.KoszulCanonicalMatrix

/-! # Canonical matrices of the finite pure-power contraction

In row-vector convention the homotopy identities read `H D + D H = 1`,
including the degree-zero right inverse. These are finite matrices over the
original commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def homotopyMatrix (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Matrix (CanonicalIndex d (Macaulay.level d) W k) (CanonicalIndex d (Macaulay.level d) W (k + 1)) R :=
  (LinearMap.toMatrix (canonicalBasis d (Macaulay.level d) W k) (canonicalBasis d (Macaulay.level d) W (k + 1))
    (weightedHomotopy d W hW k))ᵀ

theorem homotopyMatrix_identity (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    homotopyMatrix (R := R) d W hW (k + 1) *
        canonicalMatrix (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW (k + 1) +
      canonicalMatrix (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW k *
        homotopyMatrix (R := R) d W hW k = 1 := by
  unfold homotopyMatrix canonicalMatrix
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, ← Matrix.transpose_add,
    ← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp, ← map_add, weightedHomotopy_identity,
    LinearMap.toMatrix_id, Matrix.transpose_one]

theorem homotopyMatrix_zero_identity (d : Fin n → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    homotopyMatrix (R := R) d W hW 0 *
      canonicalMatrix (Macaulay.powers (R := R) d) d (Macaulay.level d) W (powers_homogeneous d) hW 0 = 1 := by
  unfold homotopyMatrix canonicalMatrix
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp, weightedHomotopy_zero_identity,
    LinearMap.toMatrix_id, Matrix.transpose_one]

end LeanCanny.Algebra.KoszulWeighted

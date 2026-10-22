/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedBasis
public import LeanCanny.Algebra.KoszulWeightedComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Canonical matrices for the finite weighted Koszul complex

The monomial–subset bases give row-vector differential matrices over any
commutative coefficient ring. Their entries are polynomial coefficients in
the ordered exterior basis. Consecutive matrices multiply to zero.
This supplies algebraic coordinates, not a resource-bounded entry reader.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def canonicalMatrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    Matrix (CanonicalIndex d L W (k + 1)) (CanonicalIndex d L W k) R :=
  (LinearMap.toMatrix (canonicalBasis d L W (k + 1)) (canonicalBasis d L W k)
    (differential p d L W hp hW k))ᵀ

theorem canonicalMatrix_apply (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ)
    (a : CanonicalIndex d L W (k + 1)) (b : CanonicalIndex d L W k) :
    canonicalMatrix p d L W hp hW k a b =
      ((exteriorBasis (R := R)).repr
        (KoszulExterior.differential p (canonicalGenerator (R := R) d L W (k + 1) a)) b.1).coeff
          (FixedWidthPolynomial.vector n W b.2.val) := by
  rw [canonicalMatrix, Matrix.transpose_apply, LinearMap.toMatrix_apply, canonicalBasis_repr_coeff]
  change ((exteriorBasis (R := R)).repr
    (KoszulExterior.differential p (canonicalBasis (R := R) d L W (k + 1) a : Total n R)) b.1).coeff _ = _
  rw [canonicalBasis_apply]

theorem canonicalMatrix_mul (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    canonicalMatrix p d L W hp hW (k + 1) * canonicalMatrix p d L W hp hW k = 0 := by
  unfold canonicalMatrix
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp, differential_comp, map_zero, Matrix.transpose_zero]

end LeanCanny.Algebra.KoszulWeighted

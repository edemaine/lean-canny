/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedComplex
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Finite matrices for the weighted Koszul complex

Over a field, the finite weighted spaces have finite bases. The differential
matrices use row-vector convention, matching the Macaulay multiplication
matrix convention. Consecutive matrices multiply to zero. The bases are
chosen noncomputably; no entry-reader or complexity bound is claimed here.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {K : Type*} [Field K]

theorem finrank_space_le (d : Fin n → ℕ) (L W k : ℕ) :
    Module.finrank K (space (R := K) d L W k) ≤ n ^ k * FixedWidthPolynomial.count n W :=
  (finrank_range_le_card (R := K) (generator (R := K) d L W k)).trans (card_index_le d L W k)

noncomputable def finiteBasis (d : Fin n → ℕ) (L W k : ℕ) :
    Module.Basis (Fin (Module.finrank K (space (R := K) d L W k))) K (space (R := K) d L W k) :=
  Module.finBasis K _

noncomputable def matrix (p : Fin n → Poly n K) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    Matrix (Fin (Module.finrank K (space (R := K) d L W (k + 1))))
      (Fin (Module.finrank K (space (R := K) d L W k))) K :=
  (LinearMap.toMatrix (finiteBasis d L W (k + 1)) (finiteBasis d L W k) (differential p d L W hp hW k))ᵀ

theorem matrix_mul (p : Fin n → Poly n K) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W) (k : ℕ) :
    matrix p d L W hp hW (k + 1) * matrix p d L W hp hW k = 0 := by
  unfold matrix
  rw [← Matrix.transpose_mul, ← LinearMap.toMatrix_comp, differential_comp, map_zero, Matrix.transpose_zero]

end LeanCanny.Algebra.KoszulWeighted

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPivotBasis
public import LeanCanny.Algebra.KoszulHomotopyOperator
public import Mathlib.LinearAlgebra.Matrix.Block

/-! # Monomial diagonal blocks of the weighted homotopy operator

The contraction preserves the pivot-containing monomial summand for every
homogeneous input system. Its canonical matrix is therefore block triangular,
and its determinant is the product of the two concrete principal blocks.
Identification of their higher Macaulay factors is a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem contractionMatrix_pivot_nonpivot (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : CanonicalIndex d (Macaulay.level d) W (k + 1))
    (ha : HasPivot d W (k + 1) a) (hb : ¬HasPivot d W (k + 1) b) :
    contractionMatrix p d W hp hW k a b = 0 := by
  have haMem : canonicalBasis (R := R) d (Macaulay.level d) W (k + 1) a ∈
      LinearMap.range (weightedHomotopy (R := R) d W hW k) := by
    rw [homotopy_range_eq_pivotSpan]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  have himg : homotopyOperator p d W hp hW k
        (canonicalBasis (R := R) d (Macaulay.level d) W (k + 1) a) ∈ pivotSpan (R := R) d W (k + 1) := by
    rw [← homotopy_range_eq_pivotSpan]
    exact homotopyOperator_mem_range p d W hp hW k _ haMem
  have hs := (canonicalBasis (R := R) d (Macaulay.level d) W (k + 1)).mem_span_image.mp himg
  rw [← homotopyOperator_matrix p d W hp hW k, Matrix.transpose_apply, LinearMap.toMatrix_apply]
  by_contra hz
  exact hb (hs (Finsupp.mem_support_iff.mpr hz))

noncomputable def pivotContractionBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :=
  Matrix.toSquareBlockProp (contractionMatrix p d W hp hW k) (HasPivot d W (k + 1))

noncomputable def nonpivotContractionBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :=
  Matrix.toSquareBlockProp (contractionMatrix p d W hp hW k) (fun a => ¬HasPivot d W (k + 1) a)

theorem contractionMatrix_det_pivot_blocks (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (contractionMatrix p d W hp hW k).det =
      (pivotContractionBlock p d W hp hW k).det * (nonpivotContractionBlock p d W hp hW k).det :=
  Matrix.twoBlockTriangular_det' _ _ (fun a ha b hb => contractionMatrix_pivot_nonpivot p d W hp hW k a b ha hb)

theorem pivot_blocks_det_ne_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (hdet : (contractionMatrix p d W hp hW k).det ≠ 0) :
    (pivotContractionBlock p d W hp hW k).det ≠ 0 ∧ (nonpivotContractionBlock p d W hp hW k).det ≠ 0 := by
  rw [contractionMatrix_det_pivot_blocks p d W hp hW k] at hdet
  exact ⟨fun hz => hdet (by rw [hz, zero_mul]), fun hz => hdet (by rw [hz, mul_zero])⟩

end LeanCanny.Algebra.KoszulWeighted

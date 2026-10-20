/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulPivotEquiv
public import LeanCanny.Algebra.KoszulPivotContraction
public import LeanCanny.Algebra.MatrixBasisConjugate

/-! # Adjacent determinant blocks of the weighted contraction

The normalized homotopy intertwines the contraction on its incoming image
with the projected contraction on the preceding nonpivot summand. The
monomial principal blocks in adjacent degrees thus have equal determinants,
over any commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem homotopyOperator_mem_pivotSpan (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (x : pivotSpan (R := R) d W (k + 1)) :
    homotopyOperator p d W hp hW k x.val ∈ pivotSpan (R := R) d W (k + 1) := by
  have hx : x.val ∈ LinearMap.range (weightedHomotopy (R := R) d W hW k) := by
    simpa only [homotopy_range_eq_pivotSpan] using x.property
  simpa only [homotopy_range_eq_pivotSpan] using
    homotopyOperator_mem_range p d W hp hW k x.val hx

noncomputable def pivotOperator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.End R (pivotSpan (R := R) d W (k + 1)) :=
  ((homotopyOperator p d W hp hW k).comp (pivotSpan d W (k + 1)).subtype).codRestrict _
    (homotopyOperator_mem_pivotSpan p d W hp hW k)

noncomputable def nonpivotOperator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.End R (nonpivotSpan (R := R) d W (k + 1)) :=
  (nonpivotProjection d W (k + 1)).comp
    ((homotopyOperator p d W hp hW k).comp (nonpivotSpan d W (k + 1)).subtype)

theorem pivotOperator_matrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (LinearMap.toMatrix (pivotBasis d W (k + 1)) (pivotBasis d W (k + 1))
      (pivotOperator p d W hp hW k))ᵀ = pivotContractionBlock p d W hp hW k := by
  ext a b
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply]
  rw [pivotBasis_repr]
  change (canonicalBasis (R := R) d (Macaulay.level d) W (k + 1)).repr
    (homotopyOperator p d W hp hW k
      (pivotBasis (R := R) d W (k + 1) a : space (R := R) d (Macaulay.level d) W (k + 1))) b.val =
    contractionMatrix p d W hp hW k a.val b.val
  rw [pivotBasis_apply, ← homotopyOperator_matrix p d W hp hW k,
    Matrix.transpose_apply, LinearMap.toMatrix_apply]

theorem nonpivotOperator_matrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (LinearMap.toMatrix (nonpivotBasis d W (k + 1)) (nonpivotBasis d W (k + 1))
      (nonpivotOperator p d W hp hW k))ᵀ = nonpivotContractionBlock p d W hp hW k := by
  ext a b
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply]
  change (nonpivotBasis (R := R) d W (k + 1)).repr
    (nonpivotProjection d W (k + 1) (homotopyOperator p d W hp hW k
      (nonpivotBasis (R := R) d W (k + 1) a : space (R := R) d (Macaulay.level d) W (k + 1)))) b =
    contractionMatrix p d W hp hW k a.val b.val
  rw [nonpivotProjection_repr, nonpivotBasis_apply,
    ← homotopyOperator_matrix p d W hp hW k, Matrix.transpose_apply, LinearMap.toMatrix_apply]

theorem pivotOperator_homotopy (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (x : nonpivotSpan (R := R) d W (k + 1)) :
    pivotOperator p d W hp hW (k + 1) (nonpivotHomotopyEquiv d W hW (k + 1) x) =
      nonpivotHomotopyEquiv d W hW (k + 1) (nonpivotOperator p d W hp hW k x) := by
  apply Subtype.ext
  change homotopyOperator p d W hp hW (k + 1)
      (nonpivotHomotopyEquiv d W hW (k + 1) x : space (R := R) d (Macaulay.level d) W (k + 2)) =
    (nonpivotHomotopyEquiv d W hW (k + 1) (nonpivotOperator p d W hp hW k x) :
      space (R := R) d (Macaulay.level d) W (k + 2))
  rw [nonpivotHomotopyEquiv_apply, nonpivotHomotopyEquiv_apply]
  change homotopyOperator p d W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x.val) =
    weightedHomotopy d W hW (k + 1)
      (nonpivotProjection d W (k + 1) (homotopyOperator p d W hp hW k x.val))
  rw [homotopy_nonpivotProjection]
  exact LinearMap.congr_fun (homotopyOperator_comp_homotopy p d W hp hW k) x.val

theorem pivotOperator_conj (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    pivotOperator p d W hp hW (k + 1) =
      (nonpivotHomotopyEquiv (R := R) d W hW (k + 1)).toLinearMap.comp
        ((nonpivotOperator p d W hp hW k).comp
          (nonpivotHomotopyEquiv (R := R) d W hW (k + 1)).symm.toLinearMap) := by
  apply LinearMap.ext
  intro y
  have he := pivotOperator_homotopy p d W hp hW k
    ((nonpivotHomotopyEquiv (R := R) d W hW (k + 1)).symm y)
  rw [LinearEquiv.apply_symm_apply] at he
  exact he

theorem adjacent_pivot_block_det (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (pivotContractionBlock p d W hp hW (k + 1)).det = (nonpivotContractionBlock p d W hp hW k).det := by
  rw [← pivotOperator_matrix p d W hp hW (k + 1), ← nonpivotOperator_matrix p d W hp hW k,
    Matrix.det_transpose, Matrix.det_transpose, pivotOperator_conj p d W hp hW k]
  -- Match the next-degree basis index syntactically to avoid unfolding the basis.
  have hc := MatrixBasisConjugate.determinant (R := R)
    (M := nonpivotSpan (R := R) d W (k + 1)) (N := pivotSpan (R := R) d W (k + 1 + 1))
    (nonpivotBasis (R := R) d W (k + 1)) (pivotBasis (R := R) d W (k + 1 + 1))
    (nonpivotHomotopyEquiv (R := R) d W hW (k + 1)) (nonpivotOperator p d W hp hW k)
  exact hc

theorem contractionMatrix_det_adjacent_blocks (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (contractionMatrix p d W hp hW (k + 1)).det =
      (nonpivotContractionBlock p d W hp hW k).det * (nonpivotContractionBlock p d W hp hW (k + 1)).det := by
  rw [contractionMatrix_det_pivot_blocks, adjacent_pivot_block_det]

end LeanCanny.Algebra.KoszulWeighted

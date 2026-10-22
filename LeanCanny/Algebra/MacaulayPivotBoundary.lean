/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulAdjacentBlocks
public import LeanCanny.Algebra.KoszulSpecializationExact
public import LeanCanny.Algebra.MacaulayHomotopyDeterminant

/-! # The initial monomial determinant block is the Macaulay numerator

The degree-zero homotopy identifies the entire degree-zero piece with the
first pivot summand. Its contraction is exactly the active Macaulay matrix
after canonical reindexing. This supplies the boundary term in the adjacent
determinant recurrence.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def zeroHomotopyEquiv (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) :
    space (R := R) d (Macaulay.level d) W 0 ≃ₗ[R] pivotSpan (R := R) d W 1 :=
  (LinearEquiv.ofInjective (weightedHomotopy (R := R) d W hW 0)
    (weightedHomotopy_zero_injective d W hW)).trans
      (LinearEquiv.ofEq _ _ (homotopy_range_eq_pivotSpan d W hW 0))

theorem zeroHomotopyEquiv_apply (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (x : space (R := R) d (Macaulay.level d) W 0) :
    (zeroHomotopyEquiv (R := R) d W hW x : space (R := R) d (Macaulay.level d) W 1) =
      weightedHomotopy d W hW 0 x := rfl

noncomputable def zeroOperator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    Module.End R (space (R := R) d (Macaulay.level d) W 0) :=
  (differential p d (Macaulay.level d) W hp hW 0).comp (weightedHomotopy d W hW 0)

theorem zeroOperator_matrix (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (LinearMap.toMatrix (canonicalBasis d (Macaulay.level d) W 0) (canonicalBasis d (Macaulay.level d) W 0)
      (zeroOperator p d W hp hW))ᵀ = zeroContractionMatrix p d W hp hW := by
  unfold zeroOperator zeroContractionMatrix homotopyMatrix canonicalMatrix
  rw [LinearMap.toMatrix_comp (canonicalBasis d (Macaulay.level d) W 0)
    (canonicalBasis d (Macaulay.level d) W 1) (canonicalBasis d (Macaulay.level d) W 0), Matrix.transpose_mul]

theorem pivotOperator_zero_conj (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    pivotOperator p d W hp hW 0 = (zeroHomotopyEquiv (R := R) d W hW).toLinearMap.comp
      ((zeroOperator p d W hp hW).comp (zeroHomotopyEquiv (R := R) d W hW).symm.toLinearMap) := by
  apply LinearMap.ext
  intro y
  let x := (zeroHomotopyEquiv (R := R) d W hW).symm y
  have hy : zeroHomotopyEquiv (R := R) d W hW x = y := LinearEquiv.apply_symm_apply _ _
  apply Subtype.ext
  change homotopyOperator p d W hp hW 0 y.val =
    (zeroHomotopyEquiv (R := R) d W hW (zeroOperator p d W hp hW x) :
      space (R := R) d (Macaulay.level d) W 1)
  rw [← hy, zeroHomotopyEquiv_apply, zeroHomotopyEquiv_apply]
  exact homotopyOperator_zero_apply_homotopy p d W hp hW x

theorem pivotBlock_zero_det (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (pivotContractionBlock p d W hp hW 0).det = (zeroContractionMatrix p d W hp hW).det := by
  rw [← pivotOperator_matrix p d W hp hW 0, ← zeroOperator_matrix p d W hp hW,
    Matrix.det_transpose, Matrix.det_transpose, pivotOperator_zero_conj p d W hp hW]
  have hc := MatrixBasisConjugate.determinant (R := R)
    (M := space (R := R) d (Macaulay.level d) W 0) (N := pivotSpan (R := R) d W (0 + 1))
    (canonicalBasis (R := R) d (Macaulay.level d) W 0) (pivotBasis (R := R) d W (0 + 1))
    (zeroHomotopyEquiv (R := R) d W hW) (zeroOperator p d W hp hW)
  exact hc

theorem zeroContractionMatrix_reindex (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (zeroContractionMatrix p d W hp hW).submatrix (macaulayTargetEquiv d W) (macaulayTargetEquiv d W) =
      Macaulay.activeMinor p d W := by
  have hm := Matrix.submatrix_mul_equiv (homotopyMatrix (R := R) d W hW 0)
    (canonicalMatrix p d (Macaulay.level d) W hp hW 0)
    (macaulayTargetEquiv d W) (macaulaySourceEquiv d W) (macaulayTargetEquiv d W)
  have hd : (canonicalMatrix p d (Macaulay.level d) W hp hW 0).submatrix
      (macaulaySourceEquiv d W) (macaulayTargetEquiv d W) = Macaulay.fullMatrix p d W :=
    canonicalMatrix_macaulay p d W hp hW
  rw [homotopyMatrix_zero_macaulay, hd,
    MatrixMinorSection.rowSelection_mul, Macaulay.fullMatrix_selected] at hm
  exact hm.symm

theorem zeroContractionMatrix_det_active (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (zeroContractionMatrix p d W hp hW).det = (Macaulay.activeMinor p d W).det := by
  have he := congrArg Matrix.det (zeroContractionMatrix_reindex p d W hp hW)
  rw [Matrix.det_submatrix_equiv_self] at he
  exact he

theorem pivotBlock_zero_det_active (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (pivotContractionBlock p d W hp hW 0).det = (Macaulay.activeMinor p d W).det := by
  rw [pivotBlock_zero_det, zeroContractionMatrix_det_active]

theorem contractionMatrix_det_initial_blocks (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (contractionMatrix p d W hp hW 0).det =
      (Macaulay.activeMinor p d W).det * (nonpivotContractionBlock p d W hp hW 0).det := by
  rw [contractionMatrix_det_pivot_blocks, pivotBlock_zero_det_active]

theorem canonicalPivot_macaulaySource (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (a : Macaulay.MultiplierIndex d W) :
    canonicalPivot d W 1 (macaulayCanonicalSource d W a) = (Macaulay.divisionRow d W hW a).1 := by
  change Macaulay.pivot d (FixedWidthPolynomial.vector n W a.2.val + subsetExponent d {a.1}) _ = _
  simpa only [subsetExponent, Finset.sum_singleton, Macaulay.productExponent] using
    (divisionRow_fst d W hW a).symm

theorem hasPivot_macaulaySource_iff (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (a : Macaulay.MultiplierIndex d W) :
    HasPivot d W 1 (macaulayCanonicalSource d W a) ↔ a ∈ Set.range (Macaulay.selectedMultiplier d W) := by
  change canonicalPivot d W 1 (macaulayCanonicalSource d W a) ∈ {a.1} ↔ _
  rw [canonicalPivot_macaulaySource d W hW a, Finset.mem_singleton]
  constructor
  · intro ha
    by_contra hn
    exact (ne_of_lt (Macaulay.divisionPivot_lt d W hW ⟨a, hn⟩)) ha
  · rintro ⟨r, rfl⟩
    simp only [Macaulay.divisionRow, Macaulay.productIndex_selected]

noncomputable def relationNonpivotEquiv (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) :
    Macaulay.RelationIndex d W ≃ {a : CanonicalIndex d (Macaulay.level d) W 1 // ¬HasPivot d W 1 a} :=
  (macaulaySourceEquiv d W).subtypeEquiv (fun a => (not_congr (hasPivot_macaulaySource_iff d W hW a)).symm)

theorem nonpivotBlock_zero_reindex (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (nonpivotContractionBlock p d W hp hW 0).submatrix
      (relationNonpivotEquiv d W hW) (relationNonpivotEquiv d W hW) = Macaulay.relationMinor p d W hW := by
  ext a b
  have he := congrFun (congrFun (contractionMatrix_zero_reindex p d W hp hW) a.val) b.val
  change contractionMatrix p d W hp hW 0 (macaulaySourceEquiv d W a.val) (macaulaySourceEquiv d W b.val) = _ at he
  rw [Matrix.add_apply, MatrixSelectedBlock.mul_rowSelection_not_mem
    (Macaulay.fullMatrix p d W) (Macaulay.selectedMultiplier d W) a.val b.val b.property, zero_add] at he
  exact he

theorem nonpivotBlock_zero_det_relation (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (nonpivotContractionBlock p d W hp hW 0).det = (Macaulay.relationMinor p d W hW).det := by
  have he := congrArg Matrix.det (nonpivotBlock_zero_reindex p d W hp hW)
  rw [Matrix.det_submatrix_equiv_self] at he
  exact he

theorem pivotBlock_one_det_relation (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (pivotContractionBlock p d W hp hW 1).det = (Macaulay.relationMinor p d W hW).det :=
  (adjacent_pivot_block_det p d W hp hW 0).trans (nonpivotBlock_zero_det_relation p d W hp hW)

theorem pivotBlock_one_det_extraneous_factor (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (pivotContractionBlock p d W hp hW 1).det =
      (Macaulay.extraneousMinor p d W).det * Macaulay.higherRelationFactor p d W hW := by
  rw [pivotBlock_one_det_relation, Macaulay.relationMinor_det_eq_extraneous_mul]

end LeanCanny.Algebra.KoszulWeighted

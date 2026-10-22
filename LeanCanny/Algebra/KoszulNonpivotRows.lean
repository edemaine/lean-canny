/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulAdjacentBlocks
public import LeanCanny.Algebra.KoszulExteriorSupport

/-! # Polynomial rows of the projected nonpivot contraction

For a nonpivot monomial/exterior index, the pivot divides its coefficient
monomial and is smaller than every exterior coordinate. Modulo the pivot
summand, the contraction is `D H`. On target subsets omitting the source
pivot, its only contribution is multiplication by the pivot input after
monomial division, with the exterior subset unchanged.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem subsetExponent_apply (d : Fin n → ℕ) (s : Finset (Fin n)) (i : Fin n) :
    subsetExponent d s i = if i ∈ s then d i else 0 := by
  simp only [subsetExponent, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_ite_eq']

theorem canonicalPivot_le_of_mem (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (j : Fin n) (hj : j ∈ a.1) :
    canonicalPivot d W k a ≤ j := by
  have he : j ∈ Macaulay.eligible d (FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finsupp.add_apply, subsetExponent_apply, ite_eq_left hj]
    exact Nat.le_add_left _ _
  exact Finset.min'_le _ _ he

theorem nonpivot_pivot_lt (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (ha : ¬HasPivot d W k a)
    (j : Fin n) (hj : j ∈ a.1) : canonicalPivot d W k a < j := by
  refine lt_of_le_of_ne (canonicalPivot_le_of_mem d W k a j hj) ?_
  intro he
  apply ha
  change canonicalPivot d W k a ∈ a.1
  rw [he]
  exact hj

theorem nonpivot_pivot_divides (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (ha : ¬HasPivot d W k a) :
    Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a)) ≤
      FixedWidthPolynomial.vector n W a.2.val := by
  apply Finsupp.single_le_iff.mpr
  have he := Macaulay.pivot_le d _ (canonical_multidegree d W k a)
  have hnot : canonicalPivot d W k a ∉ a.1 := ha
  change d (canonicalPivot d W k a) ≤
    (FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1) (canonicalPivot d W k a) at he
  simpa only [Finsupp.add_apply, subsetExponent_apply, ite_eq_right hnot, add_zero] using he

theorem levelHomotopy_nonpivot_generator (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (ha : ¬HasPivot d W k a) :
    levelHomotopy (R := R) d (canonicalGenerator (R := R) d (Macaulay.level d) W k a) =
      KoszulExterior.wedge (Pi.single (canonicalPivot d W k a) 1 : Fin n → Poly n R)
        (MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val -
          Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a))) (1 : R) •
            exteriorBasis (R := R) a.1) := by
  change levelHomotopy (R := R) d
    (ambientBasis (R := R) (FixedWidthPolynomial.vector n W a.2.val, a.1)) = _
  rw [levelHomotopy_ambientBasis, dite_eq_left (canonical_multidegree d W k a)]
  change powerHomotopy (R := R) d (canonicalPivot d W k a) _ = _
  rw [powerHomotopy_apply, divide_ambientBasis, ite_eq_left (nonpivot_pivot_divides d W k a ha), ambientBasis_apply]

theorem nonpivotProjection_homotopy (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (x : space (R := R) d (Macaulay.level d) W k) :
    nonpivotProjection (R := R) d W (k + 1) (weightedHomotopy d W hW k x) = 0 := by
  apply Submodule.projectionOnto_apply_of_mem_right
  rw [← homotopy_range_eq_pivotSpan d W hW k]
  exact LinearMap.mem_range_self _ x

theorem nonpivotOperator_eq_project_differential_homotopy (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (x : nonpivotSpan (R := R) d W (k + 1)) :
    nonpivotOperator p d W hp hW k x = nonpivotProjection d W (k + 1)
      (differential p d (Macaulay.level d) W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x.val)) := by
  change nonpivotProjection d W (k + 1)
    (differential p d (Macaulay.level d) W hp hW (k + 1) (weightedHomotopy d W hW (k + 1) x.val) +
      weightedHomotopy d W hW k (differential p d (Macaulay.level d) W hp hW k x.val)) = _
  rw [map_add, nonpivotProjection_homotopy, add_zero]

theorem nonpivotContractionBlock_apply (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // ¬HasPivot d W (k + 1) a}) :
    nonpivotContractionBlock p d W hp hW k a b =
      ((exteriorBasis (R := R)).repr (KoszulExterior.differential p
        (levelHomotopy d (canonicalGenerator (R := R) d (Macaulay.level d) W (k + 1) a.val))) b.val.1).coeff
          (FixedWidthPolynomial.vector n W b.val.2.val) := by
  rw [← nonpivotOperator_matrix p d W hp hW k, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    nonpivotOperator_eq_project_differential_homotopy, nonpivotProjection_repr, nonpivotBasis_apply,
    canonicalBasis_repr_coeff]
  change ((exteriorBasis (R := R)).repr (KoszulExterior.differential p
    (levelHomotopy d (canonicalBasis (R := R) d (Macaulay.level d) W (k + 1) a.val : Total n R))) b.val.1).coeff _ = _
  rw [canonicalBasis_apply]

theorem differential_wedge_coordinate (p : Fin n → Poly n R) (i : Fin n) (x : Total n R) :
    KoszulExterior.differential p (KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) x) =
      p i • x - KoszulExterior.wedge (Pi.single i 1 : Fin n → Poly n R) (KoszulExterior.differential p x) := by
  change KoszulExterior.differential p (ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) * x) = _
  rw [KoszulExterior.differential_ι_mul, KoszulExterior.linearForm_single]
  rfl

theorem nonpivotContractionBlock_entry_of_pivot_not_mem (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // ¬HasPivot d W (k + 1) a})
    (hi : canonicalPivot d W (k + 1) a.val ∉ b.val.1) :
    nonpivotContractionBlock p d W hp hW k a b =
      if a.val.1 = b.val.1 then
        (MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.val.2.val -
          Finsupp.single (canonicalPivot d W (k + 1) a.val) (d (canonicalPivot d W (k + 1) a.val))) (1 : R) *
            p (canonicalPivot d W (k + 1) a.val)).coeff (FixedWidthPolynomial.vector n W b.val.2.val)
      else 0 := by
  rw [nonpivotContractionBlock_apply, levelHomotopy_nonpivot_generator d W (k + 1) a.val a.property,
    differential_wedge_coordinate, map_sub, Finsupp.sub_apply,
    exteriorBasis_repr_wedge_eq_zero _ _ _ hi, sub_zero, smul_smul, exteriorBasis_repr_smul_basis]
  split_ifs
  · simp only [mul_comm]
  · rfl

end LeanCanny.Algebra.KoszulWeighted

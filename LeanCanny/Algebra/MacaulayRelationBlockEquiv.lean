/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRelationBlocks

/-! # Matching the diagonal relation blocks with the extraneous blocks

For an unreduced target monomial, divide by its greatest eligible coordinate
power. This gives the unique complementary multiplier with that coordinate.
It identifies the corresponding diagonal blocks of the two matrices.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def extraneousMultiplier (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (r : extraneousIndices d W) : RelationIndex d W := by
  let t : activeIndices d W := ⟨r.val, extraneousIndices_subset_active d W r.property⟩
  let i := extraneousLast d W r
  have hi : d i ≤ FixedWidthPolynomial.vector n W t.val i :=
    lastEligible_eligible d _ ((mem_extraneousIndices d W r.val).mp r.property).1
  let a := multiplierAt d W t i hi
  refine ⟨a, ?_⟩
  rintro ⟨s, hs⟩
  have hx := congrArg (productIndex d W hW) hs
  have hst : s = t := by
    simpa only [productIndex_selected, a, productIndex_multiplierAt] using hx
  rw [hst] at hs
  have hfirst := congrArg (fun a : MultiplierIndex d W => a.1) hs
  have hj := pivot_lt_lastEligible d _ ((mem_extraneousIndices d W r.val).mp r.property).1
    ((mem_extraneousIndices d W r.val).mp r.property).2
  exact (ne_of_lt hj) hfirst

theorem extraneousMultiplier_fst (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (r : extraneousIndices d W) : (extraneousMultiplier d W hW r).val.1 = extraneousLast d W r := rfl

theorem relationProduct_extraneousMultiplier (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (r : extraneousIndices d W) : relationProduct d W hW (extraneousMultiplier d W hW r) = r := by
  apply Subtype.ext
  let t : activeIndices d W := ⟨r.val, extraneousIndices_subset_active d W r.property⟩
  have hi : d (extraneousLast d W r) ≤ FixedWidthPolynomial.vector n W t.val (extraneousLast d W r) :=
    lastEligible_eligible d _ ((mem_extraneousIndices d W r.val).mp r.property).1
  change (productIndex d W hW (multiplierAt d W t (extraneousLast d W r) hi)).val = r.val
  exact congrArg (fun s : activeIndices d W => s.val) (productIndex_multiplierAt d W hW t _ hi)

theorem relationLast_extraneousMultiplier (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (r : extraneousIndices d W) : relationLast d W hW (extraneousMultiplier d W hW r) = extraneousLast d W r := by
  change extraneousLast d W (relationProduct d W hW (extraneousMultiplier d W hW r)) = _
  rw [relationProduct_extraneousMultiplier]

abbrev RelationCoordinateIndex (d : Fin n → ℕ) (W : ℕ) (i : Fin n) :=
  {a : RelationIndex d W // a.val.1 = i}

abbrev RelationDoubleIndex (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i k : Fin n) :=
  {a : RelationCoordinateIndex d W i // relationLast d W hW a.val = k}

noncomputable def relationCoordinateBlock (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    Matrix (RelationCoordinateIndex d W i) (RelationCoordinateIndex d W i) R :=
  (relationMinor p d W hW).toSquareBlock (fun a => a.val.1) i

noncomputable def relationDoubleBlock (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i k : Fin n) :
    Matrix (RelationDoubleIndex d W hW i k) (RelationDoubleIndex d W hW i k) R :=
  (relationCoordinateBlock p d W hW i).toSquareBlock (fun a => relationLast d W hW a.val) k

theorem relationCoordinateBlock_blockTriangular (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    (relationCoordinateBlock p d W hW i).BlockTriangular (fun a => relationLast d W hW a.val) := by
  intro a b hab
  exact relationMinor_same_component_zero_of_last_lt p d W hW a.val b.val
    (a.property.trans b.property.symm) hab

noncomputable def diagonalRelationEquiv (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    RelationDoubleIndex d W hW i i ≃ {r : extraneousIndices d W // extraneousLast d W r = i} :=
  Equiv.ofBijective (fun a => ⟨relationProduct d W hW a.val.val, a.property⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      apply relationProduct_injective_of_component_eq d W hW a.val.val b.val.val
        (a.val.property.trans b.val.property.symm)
      exact congrArg (fun r : {r : extraneousIndices d W // extraneousLast d W r = i} => r.val) h
    · intro r
      refine ⟨⟨⟨extraneousMultiplier d W hW r.val, ?_⟩, ?_⟩, ?_⟩
      · exact (extraneousMultiplier_fst d W hW r.val).trans r.property
      · exact (relationLast_extraneousMultiplier d W hW r.val).trans r.property
      · apply Subtype.ext
        exact relationProduct_extraneousMultiplier d W hW r.val)

theorem relationDoubleBlock_diagonal (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    relationDoubleBlock p d W hW i i =
      ((extraneousMinor p d W).toSquareBlock (extraneousLast d W) i).submatrix
        (diagonalRelationEquiv d W hW i) (diagonalRelationEquiv d W hW i) := by
  funext a b
  exact relationMinor_same_component p d W hW a.val.val b.val.val
    (a.val.property.trans b.val.property.symm)

theorem det_relationDoubleBlock_diagonal (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    (relationDoubleBlock p d W hW i i).det = ((extraneousMinor p d W).toSquareBlock (extraneousLast d W) i).det := by
  rw [relationDoubleBlock_diagonal, Matrix.det_submatrix_equiv_self]

end LeanCanny.Algebra.Macaulay

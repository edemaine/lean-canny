/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulNonpivotMacaulay
public import LeanCanny.Algebra.MacaulayRelationExtraneous

/-! # Higher nonpivot determinants as products of Macaulay submatrices

The projected contraction is triangular by the least exterior coordinate.
Each diagonal block is block diagonal by the full exterior subset. This
factors its determinant into concrete Macaulay principal submatrices in
every positive exterior degree, over any commutative coefficient ring.
The multiplicities needed to identify the higher extraneous factors are
not asserted here.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixBlockProduct
open scoped BigOperators Classical Matrix

theorem det_fintype_congr {R S : Type*} [CommRing R] [DecidableEq S]
    (a b : Fintype S) (M : Matrix S S R) :
    @Matrix.det S _ a R _ M = @Matrix.det S _ b R _ M := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

theorem diagonal_determinant {R S T : Type*} [CommRing R] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
    (M : Matrix S S R) (b : S → T) (h : ∀ i j, b i ≠ b j → M i j = 0) :
    M.det = ∏ t : T, (M.toSquareBlock b t).det := by
  let : LinearOrder T := LinearOrder.lift' (Fintype.equivFin T) (Fintype.equivFin T).injective
  have htri : M.BlockTriangular b := by
    intro i j hij
    apply h i j
    intro he
    exact (ne_of_lt hij) he.symm
  have hd := determinant M b htri
  refine hd.trans ?_
  apply Finset.prod_congr rfl
  intro t _
  exact det_fintype_congr _ _ _

end LeanCanny.Algebra.MatrixBlockProduct

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

abbrev NonpivotIndex (d : Fin n → ℕ) (W k : ℕ) :=
  {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // ¬HasPivot d W (k + 1) a}

theorem canonical_subset_nonempty (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W (k + 1)) : a.1.Nonempty := by
  apply Finset.card_pos.mp
  have he := ((mem_canonicalIndices d (Macaulay.level d) W (k + 1) a.1 a.2.val).mp a.2.property).1
  omega

noncomputable def nonpivotMinimum (d : Fin n → ℕ) (W k : ℕ) (a : NonpivotIndex d W k) : Fin n :=
  a.val.1.min' (canonical_subset_nonempty d W k a.val)

theorem nonpivotMinimum_mem (d : Fin n → ℕ) (W k : ℕ) (a : NonpivotIndex d W k) :
    nonpivotMinimum d W k a ∈ a.val.1 := Finset.min'_mem _ _

theorem nonpivotMinimum_le (d : Fin n → ℕ) (W k : ℕ) (a : NonpivotIndex d W k)
    (j : Fin n) (hj : j ∈ a.val.1) : nonpivotMinimum d W k a ≤ j := Finset.min'_le _ _ hj

theorem nonpivotMinimum_eq_of_subset_eq (d : Fin n → ℕ) (W k : ℕ) (a b : NonpivotIndex d W k)
    (hs : a.val.1 = b.val.1) : nonpivotMinimum d W k a = nonpivotMinimum d W k b := by
  apply le_antisymm
  · apply nonpivotMinimum_le
    rw [hs]
    exact nonpivotMinimum_mem d W k b
  · apply nonpivotMinimum_le
    rw [← hs]
    exact nonpivotMinimum_mem d W k a

theorem nonpivotContractionBlock_zero_of_minimum_le (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : NonpivotIndex d W k) (hmin : nonpivotMinimum d W k a ≤ nonpivotMinimum d W k b)
    (hne : a.val.1 ≠ b.val.1) : nonpivotContractionBlock p d W hp hW k a b = 0 := by
  have hlt : canonicalPivot d W (k + 1) a.val < nonpivotMinimum d W k a :=
    nonpivot_pivot_lt d W (k + 1) a.val a.property _ (nonpivotMinimum_mem d W k a)
  have hi : canonicalPivot d W (k + 1) a.val ∉ b.val.1 := by
    intro hmem
    exact (not_lt_of_ge (hmin.trans (nonpivotMinimum_le d W k b _ hmem))) hlt
  rw [nonpivotContractionBlock_entry_of_pivot_not_mem p d W hp hW k a b hi, ite_eq_right hne]

theorem nonpivotContractionBlock_triangular (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).BlockTriangular
      (fun a => OrderDual.toDual (nonpivotMinimum d W k a)) := by
  intro a b hab
  have hlt : nonpivotMinimum d W k a < nonpivotMinimum d W k b := hab
  apply nonpivotContractionBlock_zero_of_minimum_le p d W hp hW k a b hlt.le
  intro he
  exact (ne_of_lt hlt) (nonpivotMinimum_eq_of_subset_eq d W k a b he)

abbrev NonpivotMinimumIndex (d : Fin n → ℕ) (W k : ℕ) (i : Fin n) :=
  {a : NonpivotIndex d W k // nonpivotMinimum d W k a = i}

noncomputable def nonpivotMinimumBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (i : Fin n) :=
  (nonpivotContractionBlock p d W hp hW k).toSquareBlock (nonpivotMinimum d W k) i

theorem nonpivotContractionBlock_det_minimum (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det = ∏ i : Fin n, (nonpivotMinimumBlock p d W hp hW k i).det := by
  exact MatrixBlockProduct.determinant (nonpivotContractionBlock p d W hp hW k)
    (fun a => OrderDual.toDual (nonpivotMinimum d W k a)) (nonpivotContractionBlock_triangular p d W hp hW k)

abbrev NonpivotMinimumSubsetIndex (d : Fin n → ℕ) (W k : ℕ) (i : Fin n) (s : Finset (Fin n)) :=
  {a : NonpivotMinimumIndex d W k i // a.val.val.1 = s}

noncomputable def nonpivotMinimumSubsetBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (i : Fin n) (s : Finset (Fin n)) :=
  (nonpivotMinimumBlock p d W hp hW k i).toSquareBlock
    (fun a : NonpivotMinimumIndex d W k i => a.val.val.1) s

theorem nonpivotContractionBlock_det_subsets (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ i : Fin n, ∏ s : Finset (Fin n), (nonpivotMinimumSubsetBlock p d W hp hW k i s).det := by
  rw [nonpivotContractionBlock_det_minimum]
  apply Finset.prod_congr rfl
  intro i _
  exact MatrixBlockProduct.diagonal_determinant (R := R)
    (S := NonpivotMinimumIndex d W k i) (T := Finset (Fin n))
    (nonpivotMinimumBlock p d W hp hW k i)
    (fun a : NonpivotMinimumIndex d W k i => a.val.val.1)
    (fun a b hne => nonpivotContractionBlock_zero_of_minimum_le p d W hp hW k a.val b.val
      (le_of_eq (a.property.trans b.property.symm)) hne)

theorem nonpivotMinimumSubsetBlock_macaulay (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (i : Fin n) (s : Finset (Fin n)) :
    nonpivotMinimumSubsetBlock p d W hp hW k i s = (Macaulay.activeMinor p d W).submatrix
      (fun a : NonpivotMinimumSubsetIndex d W k i s => canonicalProductIndex d W hW (k + 1) a.val.val.val)
      (fun a : NonpivotMinimumSubsetIndex d W k i s => canonicalProductIndex d W hW (k + 1) a.val.val.val) := by
  ext a b
  exact nonpivotContractionBlock_entry_same_subset p d W hp hW k a.val.val b.val.val
    (a.property.trans b.property.symm)

theorem nonpivotMinimumSubset_productIndex_injective (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (i : Fin n) (s : Finset (Fin n)) :
    Function.Injective (fun a : NonpivotMinimumSubsetIndex d W k i s =>
      canonicalProductIndex d W hW (k + 1) a.val.val.val) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact canonicalProductIndex_injective_on_subset d W hW (k + 1) a.val.val.val b.val.val.val
    (a.property.trans b.property.symm) he

end LeanCanny.Algebra.KoszulWeighted

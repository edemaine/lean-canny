/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulNonpivotBlocks

/-! # Determinant factorization by exterior subset

The least coordinate is fixed once the exterior subset is fixed. Removing
the resulting empty factors from the two-stage triangular decomposition
gives one principal Macaulay factor for each exterior subset. Adjacent
homotopy conjugacy transfers the factorization to the next pivot block.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem nonpivotMinimum_of_subset (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) (hs : s.Nonempty)
    (a : NonpivotSubsetIndex d W k s) : nonpivotMinimum d W k a.val = s.min' hs := by
  apply le_antisymm
  · apply nonpivotMinimum_le
    rw [a.property]
    exact Finset.min'_mem s hs
  · apply Finset.min'_le
    simpa only [a.property] using nonpivotMinimum_mem d W k a.val

noncomputable def nonpivotMinimumSubsetEquiv (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) (hs : s.Nonempty) :
    NonpivotMinimumSubsetIndex d W k (s.min' hs) s ≃ NonpivotSubsetIndex d W k s where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val, nonpivotMinimum_of_subset d W k s hs a⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem nonpivotMinimumSubsetBlock_det (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    (nonpivotMinimumSubsetBlock p d W hp hW k (s.min' hs) s).det = (nonpivotSubsetBlock p d W hp hW k s).det := by
  have he : nonpivotMinimumSubsetBlock p d W hp hW k (s.min' hs) s =
      (nonpivotSubsetBlock p d W hp hW k s).submatrix
        (nonpivotMinimumSubsetEquiv d W k s hs) (nonpivotMinimumSubsetEquiv d W k s hs) := by
    ext a b
    rfl
  rw [he, Matrix.det_submatrix_equiv_self]

theorem nonpivotMinimumSubsetBlock_det_eq_one (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (s : Finset (Fin n)) (hs : s.Nonempty) (i : Fin n) (hi : i ≠ s.min' hs) :
    (nonpivotMinimumSubsetBlock p d W hp hW k i s).det = 1 := by
  have : IsEmpty (NonpivotMinimumSubsetIndex d W k i s) := ⟨fun a =>
    hi (a.val.property.symm.trans (nonpivotMinimum_of_subset d W k s hs ⟨a.val.val, a.property⟩))⟩
  exact Matrix.det_isEmpty

theorem nonpivotContractionBlock_det_exteriorSubsets (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ s : Finset (Fin n), (nonpivotSubsetBlock p d W hp hW k s).det := by
  rw [nonpivotContractionBlock_det_subsets, Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro s _
  by_cases hs : s.Nonempty
  · calc
      _ = (nonpivotMinimumSubsetBlock p d W hp hW k (s.min' hs) s).det := by
        apply Finset.prod_eq_single
        · intro i _ hi
          exact nonpivotMinimumSubsetBlock_det_eq_one p d W hp hW k s hs i hi
        · intro hn
          exact (hn (Finset.mem_univ _)).elim
      _ = _ := nonpivotMinimumSubsetBlock_det p d W hp hW k s hs
  · have : IsEmpty (NonpivotSubsetIndex d W k s) := ⟨fun a => hs (by
      rw [← a.property]
      exact canonical_subset_nonempty d W k a.val.val)⟩
    have hright : (nonpivotSubsetBlock p d W hp hW k s).det = 1 := Matrix.det_isEmpty
    rw [hright]
    apply Finset.prod_eq_one
    intro i _
    have : IsEmpty (NonpivotMinimumSubsetIndex d W k i s) := ⟨fun a =>
      IsEmpty.false (⟨a.val.val, a.property⟩ : NonpivotSubsetIndex d W k s)⟩
    exact Matrix.det_isEmpty

theorem nonpivotContractionBlock_det_macaulay (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ s : Finset (Fin n), ((Macaulay.activeMinor p d W).submatrix
        (fun a : NonpivotSubsetIndex d W k s => canonicalProductIndex d W hW (k + 1) a.val.val)
        (fun a : NonpivotSubsetIndex d W k s => canonicalProductIndex d W hW (k + 1) a.val.val)).det := by
  rw [nonpivotContractionBlock_det_exteriorSubsets]
  apply Finset.prod_congr rfl
  intro s _
  rw [nonpivotSubsetBlock_macaulay]

theorem pivotContractionBlock_det_exteriorSubsets (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (pivotContractionBlock p d W hp hW (k + 1)).det =
      ∏ s : Finset (Fin n), (nonpivotSubsetBlock p d W hp hW k s).det := by
  rw [adjacent_pivot_block_det, nonpivotContractionBlock_det_exteriorSubsets]

end LeanCanny.Algebra.KoszulWeighted

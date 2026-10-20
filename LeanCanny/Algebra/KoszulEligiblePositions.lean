/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulEligibleIndices
public import LeanCanny.Algebra.FinitePositionMasks
public import LeanCanny.Algebra.KoszulSubsetDeterminant

/-! # Position masks for the actual higher Koszul indices

At each active monomial, erase the least eligible coordinate and enumerate
the remaining coordinates in decreasing order. Nonpivot exterior indices
above that monomial correspond bijectively to position masks. Their strata
by greatest position have the required binomial cardinalities. These are
index counts; determinant compatibility with the position partition remains
a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ}

noncomputable def availableCoordinates (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) : Finset (Fin n) :=
  (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).erase (activePivot d W r)

theorem activePivot_mem (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) :
    activePivot d W r ∈ Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val) := by
  unfold activePivot Macaulay.pivot
  exact Finset.min'_mem _ _

theorem availableCoordinates_card (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) :
    (availableCoordinates d W r).card = (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card - 1 :=
  Finset.card_erase_of_mem (activePivot_mem d W r)

abbrev NonpivotProductFiber (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) :=
  {a : NonpivotIndex d W k // canonicalProductIndex d W hW (k + 1) a.val = r}

theorem nonpivotProduct_mask (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) (a : NonpivotProductFiber d W k hW r) :
    a.val.val.1 ⊆ availableCoordinates d W r ∧ a.val.val.1.card = k + 1 := by
  have he := nonpivotProduct_eligible d W k hW a.val.val.1 ⟨a.val, rfl⟩
  rw [a.property] at he
  refine ⟨?_, he.1⟩
  intro j hj
  apply Finset.mem_erase.mpr
  refine ⟨?_, he.2.1 hj⟩
  intro hji
  apply he.2.2
  simpa only [hji] using hj

noncomputable def fromEligibleMask (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W)
    (s : FinitePositionMasks.CoordinateMask (availableCoordinates d W r) (k + 1)) :
    NonpivotProductFiber d W k hW r := by
  have hr : s.val.card = k + 1 ∧ s.val ⊆ Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val) ∧
      activePivot d W r ∉ s.val := by
    refine ⟨s.property.2, ?_, ?_⟩
    · intro j hj
      exact (Finset.mem_erase.mp (s.property.1 hj)).2
    · intro hi
      exact (Finset.mem_erase.mp (s.property.1 hi)).1 rfl
  exact ⟨(fromEligibleSubset d W k s.val ⟨r, hr⟩).val, product_fromEligibleSubset d W k hW s.val ⟨r, hr⟩⟩

theorem fromEligibleMask_subset (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W)
    (s : FinitePositionMasks.CoordinateMask (availableCoordinates d W r) (k + 1)) :
    (fromEligibleMask d W k hW r s).val.val.1 = s.val := rfl

noncomputable def fiberCoordinateEquiv (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) :
    NonpivotProductFiber d W k hW r ≃ FinitePositionMasks.CoordinateMask (availableCoordinates d W r) (k + 1) :=
  Equiv.ofBijective (fun a => ⟨a.val.val.1, nonpivotProduct_mask d W k hW r a⟩)
    ⟨by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact canonicalProductIndex_injective_on_subset d W hW (k + 1) a.val.val b.val.val
        (congrArg Subtype.val he) (a.property.trans b.property.symm),
      fun s => ⟨fromEligibleMask d W k hW r s, Subtype.ext (fromEligibleMask_subset d W k hW r s)⟩⟩

noncomputable def fiberPositionEquiv (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) : NonpivotProductFiber d W k hW r ≃
      FinitePositionMasks.PositionMask (availableCoordinates d W r).card (k + 1) :=
  (fiberCoordinateEquiv d W k hW r).trans (FinitePositionMasks.coordinateMaskEquiv (availableCoordinates d W r) (k + 1))

theorem card_nonpivotProductFiber (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) : Fintype.card (NonpivotProductFiber d W k hW r) =
      ((Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card - 1).choose (k + 1) := by
  rw [Fintype.card_congr (fiberPositionEquiv d W k hW r), FinitePositionMasks.card_positionMask, availableCoordinates_card]

noncomputable def nonpivotPositionEquiv (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    NonpivotIndex d W k ≃ ((r : Macaulay.activeIndices d W) ×
      FinitePositionMasks.PositionMask (availableCoordinates d W r).card (k + 1)) :=
  (Equiv.sigmaFiberEquiv (fun a : NonpivotIndex d W k => canonicalProductIndex d W hW (k + 1) a.val)).symm.trans
    (Equiv.sigmaCongrRight (fun r => fiberPositionEquiv d W k hW r))

theorem card_nonpivotIndex (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W) :
    Fintype.card (NonpivotIndex d W k) = ∑ r : Macaulay.activeIndices d W,
      ((Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card - 1).choose (k + 1) := by
  rw [Fintype.card_congr (nonpivotPositionEquiv d W k hW), Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [FinitePositionMasks.card_positionMask, availableCoordinates_card]

abbrev EligibleLastFiber (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) (j : Fin (availableCoordinates d W r).card) :=
  {a : NonpivotProductFiber d W k hW r //
    (fiberPositionEquiv d W k hW r a).val ∈ FinitePositionMasks.lastMasks (availableCoordinates d W r).card k j}

noncomputable def eligibleLastFiberEquiv (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) (j : Fin (availableCoordinates d W r).card) :
    EligibleLastFiber d W k hW r j ≃ (FinitePositionMasks.lastMasks (availableCoordinates d W r).card k j) :=
  ((fiberPositionEquiv d W k hW r).subtypeEquiv (fun _ => Iff.rfl)).trans
    (FinitePositionMasks.lastMaskEquiv (availableCoordinates d W r).card k j)

theorem card_eligibleLastFiber (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) (j : Fin (availableCoordinates d W r).card) :
    Fintype.card (EligibleLastFiber d W k hW r j) = j.val.choose k := by
  rw [Fintype.card_congr (eligibleLastFiberEquiv d W k hW r j), Fintype.card_coe, FinitePositionMasks.card_lastMasks]

theorem exists_unique_eligibleLast (d : Fin n → ℕ) (W k : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (r : Macaulay.activeIndices d W) (a : NonpivotProductFiber d W k hW r) :
    ∃! j : Fin (availableCoordinates d W r).card,
      (fiberPositionEquiv d W k hW r a).val ∈ FinitePositionMasks.lastMasks (availableCoordinates d W r).card k j :=
  FinitePositionMasks.exists_unique_last _ _ (fiberPositionEquiv d W k hW r a)

section Matrices
variable {R : Type*} [CommRing R]

theorem nonpivotContractionBlock_det_eligible (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ s : Finset (Fin n), (eligibleSubsetBlock p d W k s).det := by
  rw [nonpivotContractionBlock_det_exteriorSubsets]
  apply Finset.prod_congr rfl
  intro s _
  exact nonpivotSubsetBlock_det_eligible p d W hp hW k s

end Matrices
end LeanCanny.Algebra.KoszulWeighted

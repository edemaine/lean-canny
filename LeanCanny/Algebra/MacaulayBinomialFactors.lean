/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullMaskComparison
public import LeanCanny.Algebra.FinitePositionMaskProduct
public import LeanCanny.Algebra.MacaulayPivotBoundary

/-! # Binomial multiplicities of the higher Macaulay minors

The degree-`k+1` nonpivot contraction determinant is the product of the
level-`j+2` eligibility determinants with exponent `Nat.choose j k`.
The identity holds over every commutative coefficient ring, including
empty index sets, without nonvanishing or genericity assumptions.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem fullMaskBlock_det_eq_one_of_card (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s m : Finset (Fin n)) (hm : m.card ≠ k + 1) : (fullMaskBlock p d W k s m).det = 1 := by
  have : IsEmpty (MaskedEligibleIndex d W k s m) := ⟨fun r => hm (by
    rw [← r.property]
    exact subsetPositionMask_card d W k s r.val)⟩
  exact Matrix.det_isEmpty

theorem nonpivotContractionBlock_det_binomial (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ j : Fin n, (Macaulay.eligibilityMinor p d W (j.val + 2)).det ^ (j.val.choose k) := by
  rw [nonpivotContractionBlock_det_fullMasks, Finset.prod_comm]
  rw [FinitePositionMasks.prod_lastMasks n k (fun m => ∏ s : Finset (Fin n), (fullMaskBlock p d W k s m).det)
    (by
      intro m hm
      apply Finset.prod_eq_one
      intro s _
      exact fullMaskBlock_det_eq_one_of_card p d W k s m hm)]
  apply Finset.prod_congr rfl
  intro j _
  calc
    (∏ m : FinitePositionMasks.lastMasks n k j, ∏ s : Finset (Fin n), (fullMaskBlock p d W k s m.val).det) =
        ∏ _m : FinitePositionMasks.lastMasks n k j, (Macaulay.eligibilityMinor p d W (j.val + 2)).det := by
      apply Finset.prod_congr rfl
      intro m _
      exact fullMask_product_eq_higherMinor p d W k j m.val m.property
    _ = (Macaulay.eligibilityMinor p d W (j.val + 2)).det ^ (j.val.choose k) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, FinitePositionMasks.card_lastMasks]

theorem pivotContractionBlock_det_binomial (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (pivotContractionBlock p d W hp hW (k + 1)).det =
      ∏ j : Fin n, (Macaulay.eligibilityMinor p d W (j.val + 2)).det ^ (j.val.choose k) := by
  rw [adjacent_pivot_block_det, nonpivotContractionBlock_det_binomial]

theorem relationMinor_det_higherMinor_product (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    (Macaulay.relationMinor p d W hW).det =
      ∏ j : Fin n, (Macaulay.eligibilityMinor p d W (j.val + 2)).det := by
  rw [← nonpivotBlock_zero_det_relation p d W hp hW, nonpivotContractionBlock_det_binomial]
  simp only [Nat.choose_zero_right, pow_one]

end LeanCanny.Algebra.KoszulWeighted

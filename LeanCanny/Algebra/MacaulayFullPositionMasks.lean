/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEligibleMonotonic
public import LeanCanny.Algebra.MatrixWeightBlockProduct

/-! # Full position-mask blocks of the higher Macaulay factors

Every selected coordinate has a decreasing eligible rank. Along a nonzero
entry in a fixed-subset factor all these ranks are nondecreasing. Equal
position sums force equality at every coordinate, hence equality of the
full masks. The determinant therefore factors over full position masks.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ}

noncomputable def eligibleCoordinatePosition (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (c : Fin n) (hc : c ∈ Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)) : Fin n := by
  let j := FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)) ⟨c, hc⟩
  have hcard : (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val))
  exact ⟨j.val, j.isLt.trans_le hcard⟩

noncomputable def subsetPositionVector (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) (c : s) : Fin n :=
  eligibleCoordinatePosition d W r.val c.val (r.property.2.1 c.property)

theorem subsetPositionVector_injective (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) : Function.Injective (subsetPositionVector d W k s r) := by
  intro x y he
  have hv := congrArg Fin.val he
  change (FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val))
      ⟨x.val, r.property.2.1 x.property⟩).val =
    (FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val))
      ⟨y.val, r.property.2.1 y.property⟩).val at hv
  have hr := (FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val))).injective
    (Fin.ext hv)
  exact Subtype.ext (congrArg
    (fun z : Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val) => z.val) hr)

noncomputable def subsetPositionMask (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) : Finset (Fin n) := Finset.univ.image (subsetPositionVector d W k s r)

theorem subsetPositionMask_card (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) : (subsetPositionMask d W k s r).card = k + 1 := by
  rw [subsetPositionMask, Finset.card_image_of_injective _ (subsetPositionVector_injective d W k s r),
    Finset.card_univ, Fintype.card_coe]
  exact r.property.1

def positionMaskWeight (m : Finset (Fin n)) : ℕ := ∑ j ∈ m, j.val

theorem positionMaskWeight_eq_sum (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) :
    positionMaskWeight (subsetPositionMask d W k s r) = ∑ c : s, (subsetPositionVector d W k s r c).val := by
  rw [positionMaskWeight, subsetPositionMask, Finset.sum_image]
  intro x _ y _ he
  exact subsetPositionVector_injective d W k s r he

section Matrices
variable {R : Type*} [CommRing R]

theorem subsetPositionVector_monotone (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (r t : EligibleSubsetIndex d W k s)
    (hentry : eligibleSubsetBlock p d W k s r t ≠ 0) (c : s) :
    subsetPositionVector d W k s r c ≤ subsetPositionVector d W k s t c := by
  change (FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val))
      ⟨c.val, r.property.2.1 c.property⟩).val ≤
    (FinitePositionMasks.reverseRank (Macaulay.eligible d (FixedWidthPolynomial.vector n W t.val.val))
      ⟨c.val, t.property.2.1 c.property⟩).val
  rw [FinitePositionMasks.reverseRank_val, FinitePositionMasks.reverseRank_val]
  exact Finset.card_le_card (eligibleAbove_subset p d W r.val t.val c.val
    (activePivot_lt_of_available d W r.val c.val (eligibleSubset_available d W k s r c.property)) hentry)

theorem subsetPositionMask_weight_monotone (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (r t : EligibleSubsetIndex d W k s)
    (hentry : eligibleSubsetBlock p d W k s r t ≠ 0) :
    positionMaskWeight (subsetPositionMask d W k s r) ≤ positionMaskWeight (subsetPositionMask d W k s t) := by
  rw [positionMaskWeight_eq_sum, positionMaskWeight_eq_sum]
  exact Finset.sum_le_sum (fun c _ => subsetPositionVector_monotone p d W k s r t hentry c)

theorem subsetPositionMask_eq_of_weight_eq (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (r t : EligibleSubsetIndex d W k s)
    (hentry : eligibleSubsetBlock p d W k s r t ≠ 0)
    (he : positionMaskWeight (subsetPositionMask d W k s r) = positionMaskWeight (subsetPositionMask d W k s t)) :
    subsetPositionMask d W k s r = subsetPositionMask d W k s t := by
  rw [positionMaskWeight_eq_sum, positionMaskWeight_eq_sum] at he
  have hv : subsetPositionVector d W k s r = subsetPositionVector d W k s t := by
    funext c
    apply Fin.ext
    have hcoord (i : s) : (subsetPositionVector d W k s r i).val ≤ (subsetPositionVector d W k s t i).val :=
      subsetPositionVector_monotone p d W k s r t hentry i
    exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hcoord i)).mp he c (Finset.mem_univ c)
  exact congrArg (fun f : s → Fin n => Finset.univ.image f) hv

abbrev MaskedEligibleIndex (d : Fin n → ℕ) (W k : ℕ) (s m : Finset (Fin n)) :=
  {r : EligibleSubsetIndex d W k s // subsetPositionMask d W k s r = m}

noncomputable def fullMaskBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s m : Finset (Fin n)) := (eligibleSubsetBlock p d W k s).toSquareBlock (subsetPositionMask d W k s) m

theorem eligibleSubsetBlock_det_fullMasks (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) : (eligibleSubsetBlock p d W k s).det =
      ∏ m : Finset (Fin n), (fullMaskBlock p d W k s m).det := by
  exact MatrixBlockProduct.determinant_of_weight (R := R) (S := EligibleSubsetIndex d W k s) (T := Finset (Fin n))
    (eligibleSubsetBlock p d W k s) (subsetPositionMask d W k s) positionMaskWeight
    (subsetPositionMask_weight_monotone p d W k s) (subsetPositionMask_eq_of_weight_eq p d W k s)

theorem nonpivotContractionBlock_det_fullMasks (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (nonpivotContractionBlock p d W hp hW k).det =
      ∏ s : Finset (Fin n), ∏ m : Finset (Fin n), (fullMaskBlock p d W k s m).det := by
  rw [nonpivotContractionBlock_det_eligible]
  apply Finset.prod_congr rfl
  intro s _
  exact eligibleSubsetBlock_det_fullMasks p d W k s

end Matrices
end LeanCanny.Algebra.KoszulWeighted

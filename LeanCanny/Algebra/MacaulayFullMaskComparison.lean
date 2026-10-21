/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayMaskedLevelIndices

/-! # Full-mask factors are higher Macaulay minors

Fix a position mask with greatest position `j`. Its decoded exterior
coordinates are nondecreasing along nonzero entries of the level-`j+2`
minor. Their sum orders the exterior-subset blocks. Reindexing these
diagonal blocks identifies their determinant product with that minor.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ}

noncomputable def decodedCoordinate (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) (i : m) : Fin n :=
  FinitePositionMasks.positionAt (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val))
    m (levelMask_bound d W k j m hm r) i

theorem decodedCoordinate_mem (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) (i : m) :
    decodedCoordinate d W k j m hm r i ∈ decodedSubset d W k j m hm r :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem decodedCoordinate_injective (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    Function.Injective (decodedCoordinate d W k j m hm r) :=
  FinitePositionMasks.positionAt_injective _ _ (levelMask_bound d W k j m hm r)

theorem decodedSubset_weight_eq_sum (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    positionMaskWeight (decodedSubset d W k j m hm r) = ∑ i : m, (decodedCoordinate d W k j m hm r i).val := by
  change positionMaskWeight (Finset.univ.image (decodedCoordinate d W k j m hm r)) = _
  rw [positionMaskWeight,
    Finset.sum_image (fun x _ y _ he => decodedCoordinate_injective d W k j m hm r he)]

variable {R : Type*} [CommRing R]

theorem decodedCoordinate_monotone (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j)
    (r t : Macaulay.eligibilityIndices d W (j.val + 2))
    (hentry : Macaulay.eligibilityMinor p d W (j.val + 2) r t ≠ 0) (i : m) :
    decodedCoordinate d W k j m hm r i ≤ decodedCoordinate d W k j m hm t i := by
  let A := Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)
  let B := Macaulay.eligible d (FixedWidthPolynomial.vector n W t.val)
  let c := decodedCoordinate d W k j m hm r i
  have hc := eligibleSubset_available d W k (decodedSubset d W k j m hm r)
    (decodedEligibleIndex d W k j m hm r) (decodedCoordinate_mem d W k j m hm r i)
  have hcB : c ∈ B := availableCoordinates_preserved p d W
    (eligibilityActiveIndex d W (j.val + 2) r) (eligibilityActiveIndex d W (j.val + 2) t) hentry hc
  apply FinitePositionMasks.positionAt_le_of_rank_le A B m
    (levelMask_bound d W k j m hm r) (levelMask_bound d W k j m hm t) i hcB
  have hr := congrArg (fun u : Fin A.card => u.val)
    (FinitePositionMasks.positionAt_rank A m (levelMask_bound d W k j m hm r) i)
  change (FinitePositionMasks.reverseRank A ⟨c, _⟩).val = i.val.val at hr
  rw [FinitePositionMasks.reverseRank_val] at hr
  calc
    i.val.val = (A.filter (c < ·)).card := hr.symm
    _ ≤ (B.filter (c < ·)).card := Finset.card_le_card (eligibleAbove_subset p d W
      (eligibilityActiveIndex d W (j.val + 2) r) (eligibilityActiveIndex d W (j.val + 2) t) c
      (activePivot_lt_of_available d W (eligibilityActiveIndex d W (j.val + 2) r) c hc) hentry)
    _ = (FinitePositionMasks.reverseRank B ⟨c, hcB⟩).val := (FinitePositionMasks.reverseRank_val B ⟨c, hcB⟩).symm

theorem decodedSubset_weight_monotone (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j)
    (r t : Macaulay.eligibilityIndices d W (j.val + 2))
    (hentry : Macaulay.eligibilityMinor p d W (j.val + 2) r t ≠ 0) :
    positionMaskWeight (decodedSubset d W k j m hm r) ≤ positionMaskWeight (decodedSubset d W k j m hm t) := by
  rw [decodedSubset_weight_eq_sum, decodedSubset_weight_eq_sum]
  exact Finset.sum_le_sum (fun i _ => decodedCoordinate_monotone p d W k j m hm r t hentry i)

theorem decodedSubset_eq_of_weight_eq (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j)
    (r t : Macaulay.eligibilityIndices d W (j.val + 2))
    (hentry : Macaulay.eligibilityMinor p d W (j.val + 2) r t ≠ 0)
    (he : positionMaskWeight (decodedSubset d W k j m hm r) = positionMaskWeight (decodedSubset d W k j m hm t)) :
    decodedSubset d W k j m hm r = decodedSubset d W k j m hm t := by
  rw [decodedSubset_weight_eq_sum, decodedSubset_weight_eq_sum] at he
  have hv : decodedCoordinate d W k j m hm r = decodedCoordinate d W k j m hm t := by
    funext i
    apply Fin.ext
    have hcoord (a : m) : (decodedCoordinate d W k j m hm r a).val ≤ (decodedCoordinate d W k j m hm t a).val :=
      decodedCoordinate_monotone p d W k j m hm r t hentry a
    exact (Finset.sum_eq_sum_iff_of_le (fun a _ => hcoord a)).mp he i (Finset.mem_univ i)
  exact congrArg (fun f : m → Fin n => Finset.univ.image f) hv

theorem eligibilityMinor_det_decodedSubsets (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j) :
    (Macaulay.eligibilityMinor p d W (j.val + 2)).det = ∏ s : Finset (Fin n),
      ((Macaulay.eligibilityMinor p d W (j.val + 2)).toSquareBlock (decodedSubset d W k j m hm) s).det :=
  MatrixBlockProduct.determinant_of_weight (R := R) (S := Macaulay.eligibilityIndices d W (j.val + 2))
    (T := Finset (Fin n)) (Macaulay.eligibilityMinor p d W (j.val + 2)) (decodedSubset d W k j m hm)
    positionMaskWeight (decodedSubset_weight_monotone p d W k j m hm) (decodedSubset_eq_of_weight_eq p d W k j m hm)

theorem fullMaskBlock_det_decodedBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j) (s : Finset (Fin n)) :
    (fullMaskBlock p d W k s m).det =
      ((Macaulay.eligibilityMinor p d W (j.val + 2)).toSquareBlock (decodedSubset d W k j m hm) s).det := by
  let e := fixedMaskBlockEquiv d W k j m hm s
  have he : ((Macaulay.eligibilityMinor p d W (j.val + 2)).toSquareBlock
      (decodedSubset d W k j m hm) s).submatrix e e = fullMaskBlock p d W k s m := by
    ext a b
    rfl
  rw [← he, Matrix.det_submatrix_equiv_self]

theorem fullMask_product_eq_higherMinor (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (j : Fin n) (m : Finset (Fin n)) (hm : m ∈ FinitePositionMasks.lastMasks n k j) :
    (∏ s : Finset (Fin n), (fullMaskBlock p d W k s m).det) = (Macaulay.eligibilityMinor p d W (j.val + 2)).det := by
  rw [eligibilityMinor_det_decodedSubsets p d W k j m hm]
  apply Finset.prod_congr rfl
  intro s _
  exact fullMaskBlock_det_decodedBlock p d W k j m hm s

end LeanCanny.Algebra.KoszulWeighted

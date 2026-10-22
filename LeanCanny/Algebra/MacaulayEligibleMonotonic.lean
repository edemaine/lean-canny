/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulEligiblePositions
public import LeanCanny.Algebra.MacaulayEligibilityLevels

/-! # Triangularity by the greatest selected eligible position

A nonzero active Macaulay entry preserves every eligible coordinate except
possibly its source pivot. Hence the decreasing position of any selected
nonpivot coordinate cannot decrease. For each fixed nonempty exterior
subset, this makes the eligible principal submatrix triangular by the
greatest selected position, giving a further determinant decomposition.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem eligibleLast_threshold (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (j : Fin (availableCoordinates d W r).card) :
    j.val + 2 ≤ (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card := by
  have hj := j.isLt
  have hcard := availableCoordinates_card d W r
  omega

noncomputable def eligibleLastLevelIndex (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (j : Fin (availableCoordinates d W r).card) : Macaulay.eligibilityIndices d W (j.val + 2) :=
  ⟨r.val, (Macaulay.mem_eligibilityIndices d W (j.val + 2) r.val).mpr
    ⟨(Macaulay.mem_activeIndices d W r.val).mp r.property, eligibleLast_threshold d W r j⟩⟩

theorem remainder_le_of_active_entry_ne_zero (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (r t : Macaulay.activeIndices d W) (hentry : Macaulay.activeMinor p d W r t ≠ 0) :
    Macaulay.remainder d (FixedWidthPolynomial.vector n W r.val)
      ((Macaulay.mem_activeIndices d W r.val).mp r.property) ≤ FixedWidthPolynomial.vector n W t.val := by
  change Macaulay.matrix p d W r.val t.val ≠ 0 at hentry
  by_contra hn
  rw [Macaulay.entry_active p d W r.val t.val ((Macaulay.mem_activeIndices d W r.val).mp r.property),
    ite_eq_right hn] at hentry
  exact hentry rfl

theorem availableCoordinates_preserved (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (r t : Macaulay.activeIndices d W) (hentry : Macaulay.activeMinor p d W r t ≠ 0) :
    availableCoordinates d W r ⊆ Macaulay.eligible d (FixedWidthPolynomial.vector n W t.val) := by
  intro j hj
  have hs := Finset.mem_erase.mp hj
  have hcoord := remainder_le_of_active_entry_ne_zero p d W r t hentry j
  change (FixedWidthPolynomial.vector n W r.val - Finsupp.single (activePivot d W r) (d (activePivot d W r))) j ≤
    FixedWidthPolynomial.vector n W t.val j at hcoord
  rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hs.1, Nat.sub_zero] at hcoord
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs.2).2.trans hcoord⟩

theorem activePivot_lt_of_available (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (c : Fin n) (hc : c ∈ availableCoordinates d W r) : activePivot d W r < c := by
  have hs := Finset.mem_erase.mp hc
  have hle : activePivot d W r ≤ c := by
    unfold activePivot Macaulay.pivot
    exact Finset.min'_le _ _ hs.2
  exact lt_of_le_of_ne hle (Ne.symm hs.1)

theorem availableAbove_eq (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (c : Fin n) (hc : activePivot d W r < c) :
    (availableCoordinates d W r).filter (fun j => c < j) =
      (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).filter (fun j => c < j) := by
  ext j
  simp only [availableCoordinates, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hj⟩, hlt⟩
    exact ⟨hj, hlt⟩
  · rintro ⟨hj, hlt⟩
    exact ⟨⟨ne_of_gt (hc.trans hlt), hj⟩, hlt⟩

theorem eligibleAbove_subset (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (r t : Macaulay.activeIndices d W) (c : Fin n) (hc : activePivot d W r < c)
    (hentry : Macaulay.activeMinor p d W r t ≠ 0) :
    (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).filter (fun j => c < j) ⊆
      (Macaulay.eligible d (FixedWidthPolynomial.vector n W t.val)).filter (fun j => c < j) := by
  intro j hj
  have hs := Finset.mem_filter.mp hj
  apply Finset.mem_filter.mpr
  exact ⟨availableCoordinates_preserved p d W r t hentry
    (Finset.mem_erase.mpr ⟨ne_of_gt (hc.trans hs.2), hs.1⟩), hs.2⟩

theorem availablePosition_monotone (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (r t : Macaulay.activeIndices d W) (c : Fin n)
    (hr : c ∈ availableCoordinates d W r) (ht : c ∈ availableCoordinates d W t)
    (hentry : Macaulay.activeMinor p d W r t ≠ 0) :
    (FinitePositionMasks.reverseRank (availableCoordinates d W r) ⟨c, hr⟩).val ≤
      (FinitePositionMasks.reverseRank (availableCoordinates d W t) ⟨c, ht⟩).val := by
  rw [FinitePositionMasks.reverseRank_val, FinitePositionMasks.reverseRank_val,
    availableAbove_eq d W r c (activePivot_lt_of_available d W r c hr),
    availableAbove_eq d W t c (activePivot_lt_of_available d W t c ht)]
  exact Finset.card_le_card (eligibleAbove_subset p d W r t c (activePivot_lt_of_available d W r c hr) hentry)

theorem eligibleSubset_available (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) : s ⊆ availableCoordinates d W r.val := by
  intro c hc
  apply Finset.mem_erase.mpr
  refine ⟨?_, r.property.2.1 hc⟩
  intro he
  apply r.property.2.2
  simpa only [he] using hc

noncomputable def eligibleLastPosition (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) (hs : s.Nonempty)
    (r : EligibleSubsetIndex d W k s) : Fin n := by
  let j := FinitePositionMasks.reverseRank (availableCoordinates d W r.val)
    ⟨s.min' hs, eligibleSubset_available d W k s r (Finset.min'_mem s hs)⟩
  have hcard : (availableCoordinates d W r.val).card ≤ n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (availableCoordinates d W r.val)
  exact ⟨j.val, j.isLt.trans_le hcard⟩

theorem eligibleSubsetBlock_position_triangular (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    (eligibleSubsetBlock p d W k s).BlockTriangular (eligibleLastPosition d W k s hs) := by
  intro r t hlt
  by_contra hentry
  have hle := availablePosition_monotone p d W r.val t.val (s.min' hs)
    (eligibleSubset_available d W k s r (Finset.min'_mem s hs))
    (eligibleSubset_available d W k s t (Finset.min'_mem s hs)) hentry
  exact (not_lt_of_ge hle) hlt

theorem eligibleSubsetBlock_det_positions (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (hs : s.Nonempty) :
    (eligibleSubsetBlock p d W k s).det = ∏ j : Fin n,
      ((eligibleSubsetBlock p d W k s).toSquareBlock (eligibleLastPosition d W k s hs) j).det :=
  MatrixBlockProduct.determinant _ _ (eligibleSubsetBlock_position_triangular p d W k s hs)

theorem eligibleSubset_mask_last (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) (hs : s.Nonempty)
    (r : EligibleSubsetIndex d W k s) :
    (FinitePositionMasks.coordinateMaskEquiv (availableCoordinates d W r.val) (k + 1)
      ⟨s, eligibleSubset_available d W k s r, r.property.1⟩).val ∈
        FinitePositionMasks.lastMasks (availableCoordinates d W r.val).card k
          (FinitePositionMasks.reverseRank (availableCoordinates d W r.val)
            ⟨s.min' hs, eligibleSubset_available d W k s r (Finset.min'_mem s hs)⟩) :=
  FinitePositionMasks.coordinateMask_mem_last _ _ _ _ (Finset.min'_mem s hs) (fun _ hi => Finset.min'_le s _ hi)

end LeanCanny.Algebra.KoszulWeighted

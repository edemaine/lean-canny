/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayFullPositionMasks
public import LeanCanny.Algebra.FinitePositionSelection

/-! # A fixed full mask parametrizes a higher eligibility level

A mask of cardinality `k+1` with greatest position `j` selects one exterior
subset at each active monomial with at least `j+2` eligible coordinates.
Encoding and decoding give an exact bijection between the union of the
fixed-subset mask indices and the concrete level-`j+2` Macaulay indices.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ}

theorem eligibility_card_le (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) :
    (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card ≤ n := by
  simpa only [Fintype.card_fin] using Finset.card_le_univ (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val))

theorem subsetPositionMask_eq_encode (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) : subsetPositionMask d W k s r =
      FinitePositionMasks.encodePositions (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val))
        s r.property.2.1 n (eligibility_card_le d W r.val) := rfl

theorem eligibleCoordinatePosition_margin (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W)
    (c : Fin n) (hc : c ∈ availableCoordinates d W r) :
    (eligibleCoordinatePosition d W r c (Finset.mem_erase.mp hc).2).val + 2 ≤
      (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card := by
  let A := Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)
  let x : A := ⟨c, (Finset.mem_erase.mp hc).2⟩
  let p : A := ⟨activePivot d W r, activePivot_mem d W r⟩
  have hlt : FinitePositionMasks.reverseRank A x < FinitePositionMasks.reverseRank A p :=
    (FinitePositionMasks.reverseRank_lt_iff A x p).mpr (activePivot_lt_of_available d W r c hc)
  have hnat : (FinitePositionMasks.reverseRank A x).val < (FinitePositionMasks.reverseRank A p).val := hlt
  have hb := (FinitePositionMasks.reverseRank A p).isLt
  change (FinitePositionMasks.reverseRank A x).val + 2 ≤ A.card
  omega

theorem subsetPositionMask_margin (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n))
    (r : EligibleSubsetIndex d W k s) (j : Fin n) (hj : j ∈ subsetPositionMask d W k s r) :
    j.val + 2 ≤ (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val)).card := by
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hj
  exact eligibleCoordinatePosition_margin d W r.val c.val (eligibleSubset_available d W k s r c.property)

noncomputable def maskedLevelIndex (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (s : Finset (Fin n)) (r : MaskedEligibleIndex d W k s m) :
    Macaulay.eligibilityIndices d W (j.val + 2) := by
  have hj : j ∈ subsetPositionMask d W k s r.val := by
    rw [r.property]
    exact ((FinitePositionMasks.mem_lastMasks n k j m).mp hm).2.2
  exact ⟨r.val.val.val, (Macaulay.mem_eligibilityIndices d W (j.val + 2) _).mpr
    ⟨(Macaulay.mem_activeIndices d W _).mp r.val.val.property, subsetPositionMask_margin d W k s r.val j hj⟩⟩

noncomputable def eligibilityActiveIndex (d : Fin n → ℕ) (W h : ℕ) (r : Macaulay.eligibilityIndices d W h) :
    Macaulay.activeIndices d W := ⟨r.val, Macaulay.eligibilityIndices_subset_active d W h r.property⟩

theorem levelMask_margin (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    ∀ i ∈ m, i.val + 2 ≤ (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card := by
  intro i hi
  have hij : i ≤ j := Finset.mem_Iic.mp (((FinitePositionMasks.mem_lastMasks n k j m).mp hm).1 hi)
  have hij' : i.val ≤ j.val := hij
  have hcard := ((Macaulay.mem_eligibilityIndices d W (j.val + 2) r.val).mp r.property).2
  omega

theorem levelMask_bound (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    ∀ i ∈ m, i.val < (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val)).card := by
  intro i hi
  have he := levelMask_margin d W k j m hm r i hi
  omega

noncomputable def decodedSubset (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) : Finset (Fin n) :=
  FinitePositionMasks.selectPositions (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val))
    m (levelMask_bound d W k j m hm r)

theorem decodedSubset_eligible (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    decodedSubset d W k j m hm r ⊆ Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val) :=
  FinitePositionMasks.selectPositions_subset _ _ _

theorem decodedSubset_card (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    (decodedSubset d W k j m hm r).card = k + 1 := by
  rw [decodedSubset, FinitePositionMasks.selectPositions_card]
  exact ((FinitePositionMasks.mem_lastMasks n k j m).mp hm).2.1

theorem decodedSubset_omits_pivot (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    activePivot d W (eligibilityActiveIndex d W (j.val + 2) r) ∉ decodedSubset d W k j m hm r := by
  apply FinitePositionMasks.min_not_mem_selectPositions _ _ (levelMask_bound d W k j m hm r)
    (levelMask_margin d W k j m hm r) ⟨_, activePivot_mem d W (eligibilityActiveIndex d W (j.val + 2) r)⟩
  intro y hy
  unfold activePivot Macaulay.pivot
  exact Finset.min'_le _ _ hy

noncomputable def decodedEligibleIndex (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    EligibleSubsetIndex d W k (decodedSubset d W k j m hm r) :=
  ⟨eligibilityActiveIndex d W (j.val + 2) r, decodedSubset_card d W k j m hm r,
    decodedSubset_eligible d W k j m hm r, decodedSubset_omits_pivot d W k j m hm r⟩

theorem decodedPositionMask (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (r : Macaulay.eligibilityIndices d W (j.val + 2)) :
    subsetPositionMask d W k (decodedSubset d W k j m hm r) (decodedEligibleIndex d W k j m hm r) = m := by
  rw [subsetPositionMask_eq_encode]
  exact FinitePositionMasks.encode_selectPositions _ _ _ _

theorem decodedSubset_maskedLevelIndex (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (s : Finset (Fin n)) (r : MaskedEligibleIndex d W k s m) :
    decodedSubset d W k j m hm (maskedLevelIndex d W k j m hm s r) = s := by
  have he := FinitePositionMasks.select_encodePositions
    (Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val.val.val)) s r.val.property.2.1 n
    (eligibility_card_le d W r.val.val)
  have hmask := (subsetPositionMask_eq_encode d W k s r.val).symm.trans r.property
  simp only [hmask] at he
  exact he

noncomputable def maskedLevelEquiv (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) :
    ((s : Finset (Fin n)) × MaskedEligibleIndex d W k s m) ≃ Macaulay.eligibilityIndices d W (j.val + 2) :=
  Equiv.ofBijective (fun a => maskedLevelIndex d W k j m hm a.1 a.2)
    ⟨by
      rintro ⟨s, a⟩ ⟨t, b⟩ he
      have hs : s = t := (decodedSubset_maskedLevelIndex d W k j m hm s a).symm.trans
        ((congrArg (decodedSubset d W k j m hm) he).trans (decodedSubset_maskedLevelIndex d W k j m hm t b))
      subst t
      apply congrArg (Sigma.mk s)
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun r : Macaulay.eligibilityIndices d W (j.val + 2) => r.val) he,
      fun r => ⟨⟨decodedSubset d W k j m hm r, ⟨decodedEligibleIndex d W k j m hm r, decodedPositionMask d W k j m hm r⟩⟩,
        Subtype.ext rfl⟩⟩

noncomputable def fixedMaskBlockEquiv (d : Fin n → ℕ) (W k : ℕ) (j : Fin n) (m : Finset (Fin n))
    (hm : m ∈ FinitePositionMasks.lastMasks n k j) (s : Finset (Fin n)) :
    MaskedEligibleIndex d W k s m ≃
      {r : Macaulay.eligibilityIndices d W (j.val + 2) // decodedSubset d W k j m hm r = s} :=
  Equiv.ofBijective (fun r => ⟨maskedLevelIndex d W k j m hm s r,
    decodedSubset_maskedLevelIndex d W k j m hm s r⟩)
    ⟨by
      intro a b he
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun r : {r : Macaulay.eligibilityIndices d W (j.val + 2) //
        decodedSubset d W k j m hm r = s} => r.val.val) he,
      by
        intro r
        obtain ⟨⟨t, u⟩, hu⟩ := (maskedLevelEquiv d W k j m hm).surjective r.val
        have ht : t = s := (decodedSubset_maskedLevelIndex d W k j m hm t u).symm.trans
          ((congrArg (decodedSubset d W k j m hm) hu).trans r.property)
        subst t
        exact ⟨u, Subtype.ext hu⟩⟩

end LeanCanny.Algebra.KoszulWeighted

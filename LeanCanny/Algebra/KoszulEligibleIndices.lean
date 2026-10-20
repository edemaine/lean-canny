/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulNonpivotMacaulay

/-! # Eligible-coordinate description of the higher Macaulay factors

For a fixed exterior subset, the nonpivot monomial indices correspond
exactly to active monomials for which every exterior coordinate is eligible
and the least eligible coordinate is omitted. The inverse subtracts the
exterior coordinate powers. This describes the principal submatrices
without referring to exterior-algebra coordinates.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ}

theorem subsetExponent_degree (d : Fin n → ℕ) (s : Finset (Fin n)) :
    (subsetExponent d s).degree = subsetWeight d s := by
  simp only [subsetExponent, map_sum, Finsupp.degree_single, subsetWeight]

theorem subsetExponent_le_iff (d : Fin n → ℕ) (s : Finset (Fin n)) (t : Fin n →₀ ℕ) :
    subsetExponent d s ≤ t ↔ s ⊆ Macaulay.eligible d t := by
  constructor
  · intro h i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have he := h i
    simpa only [subsetExponent_apply, ite_eq_left hi] using he
  · intro h i
    rw [subsetExponent_apply]
    split_ifs with hi
    · exact (Finset.mem_filter.mp (h hi)).2
    · exact Nat.zero_le _

noncomputable def activePivot (d : Fin n → ℕ) (W : ℕ) (r : Macaulay.activeIndices d W) : Fin n :=
  Macaulay.pivot d (FixedWidthPolynomial.vector n W r.val) ((Macaulay.mem_activeIndices d W r.val).mp r.property)

abbrev EligibleSubsetIndex (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) :=
  {r : Macaulay.activeIndices d W // s.card = k + 1 ∧
    s ⊆ Macaulay.eligible d (FixedWidthPolynomial.vector n W r.val) ∧ activePivot d W r ∉ s}

theorem canonical_subset_eligible (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (a : CanonicalIndex d (Macaulay.level d) W k) :
    a.1 ⊆ Macaulay.eligible d (FixedWidthPolynomial.vector n W (canonicalProductIndex d W hW k a).val) := by
  rw [← subsetExponent_le_iff, vector_canonicalProductIndex]
  exact le_add_self

theorem nonpivotProduct_eligible (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (s : Finset (Fin n)) (a : NonpivotSubsetIndex d W k s) :
    s.card = k + 1 ∧ s ⊆ Macaulay.eligible d
      (FixedWidthPolynomial.vector n W (canonicalProductIndex d W hW (k + 1) a.val.val).val) ∧
        activePivot d W (canonicalProductIndex d W hW (k + 1) a.val.val) ∉ s := by
  refine ⟨?_, ?_, ?_⟩
  · have he := ((mem_canonicalIndices d (Macaulay.level d) W (k + 1)
      a.val.val.1 a.val.val.2.val).mp a.val.val.2.property).1
    simpa only [a.property] using he
  · simpa only [a.property] using canonical_subset_eligible d W (k + 1) hW a.val.val
  · have he : canonicalPivot d W (k + 1) a.val.val ∉ a.val.val.1 := a.val.property
    change Macaulay.pivot d _ _ ∉ s
    simpa only [pivot_canonicalProductIndex, a.property] using he

noncomputable def fromEligibleSubset (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (r : EligibleSubsetIndex d W k s) :
    NonpivotSubsetIndex d W k s := by
  let t := FixedWidthPolynomial.vector n W r.val.val
  let m := t - subsetExponent d s
  have hle : subsetExponent d s ≤ t := (subsetExponent_le_iff d s t).mpr r.property.2.1
  have hm : m + subsetExponent d s = t := tsub_add_cancel_of_le hle
  have hb (j : Fin n) : m j < 2 ^ W := by
    change (t - subsetExponent d s) j < 2 ^ W
    rw [Finsupp.tsub_apply]
    exact (Nat.sub_le _ _).trans_lt (FixedWidthPolynomial.vector_lt n W r.val.val j)
  let rank := FixedWidthPolynomial.index n W m hb
  have hrank : rank ∈ canonicalIndices d (Macaulay.level d) W (k + 1) s := by
    rw [mem_canonicalIndices, FixedWidthPolynomial.vector_index]
    refine ⟨r.property.1, ?_⟩
    have he := congrArg Finsupp.degree hm
    rw [map_add, subsetExponent_degree] at he
    exact he.trans ((Macaulay.mem_activeIndices d W r.val.val).mp r.val.property)
  let a : CanonicalIndex d (Macaulay.level d) W (k + 1) := ⟨s, rank, hrank⟩
  have ha : ¬HasPivot d W (k + 1) a := by
    change Macaulay.pivot d (FixedWidthPolynomial.vector n W rank + subsetExponent d s) _ ∉ s
    simpa only [rank, FixedWidthPolynomial.vector_index, hm, activePivot] using r.property.2.2
  exact ⟨⟨a, ha⟩, rfl⟩

theorem fromEligibleSubset_vector (d : Fin n → ℕ) (W k : ℕ)
    (s : Finset (Fin n)) (r : EligibleSubsetIndex d W k s) :
    FixedWidthPolynomial.vector n W (fromEligibleSubset d W k s r).val.val.2.val =
      FixedWidthPolynomial.vector n W r.val.val - subsetExponent d s :=
  FixedWidthPolynomial.vector_index n W _ _

theorem product_fromEligibleSubset (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (s : Finset (Fin n)) (r : EligibleSubsetIndex d W k s) :
    canonicalProductIndex d W hW (k + 1) (fromEligibleSubset d W k s r).val.val = r.val := by
  apply Subtype.ext
  apply FixedWidthPolynomial.vector_injective n W
  rw [vector_canonicalProductIndex, fromEligibleSubset_vector]
  change (FixedWidthPolynomial.vector n W r.val.val - subsetExponent d s) + subsetExponent d s = _
  exact tsub_add_cancel_of_le ((subsetExponent_le_iff d s _).mpr r.property.2.1)

noncomputable def nonpivotEligibleEquiv (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (s : Finset (Fin n)) :
    NonpivotSubsetIndex d W k s ≃ EligibleSubsetIndex d W k s :=
  Equiv.ofBijective
    (fun a => ⟨canonicalProductIndex d W hW (k + 1) a.val.val, nonpivotProduct_eligible d W k hW s a⟩)
    ⟨fun _ _ he => nonpivotSubset_productIndex_injective d W hW k s (congrArg Subtype.val he),
      fun r => ⟨fromEligibleSubset d W k s r, Subtype.ext (product_fromEligibleSubset d W k hW s r)⟩⟩

section Matrices
variable {R : Type*} [CommRing R]

noncomputable def eligibleSubsetBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) :=
  (Macaulay.activeMinor p d W).submatrix (fun r : EligibleSubsetIndex d W k s => r.val)
    (fun r : EligibleSubsetIndex d W k s => r.val)

theorem eligibleSubsetBlock_reindex (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (s : Finset (Fin n)) :
    (eligibleSubsetBlock p d W k s).submatrix (nonpivotEligibleEquiv d W k hW s) (nonpivotEligibleEquiv d W k hW s) =
      nonpivotSubsetBlock p d W hp hW k s := by
  ext a b
  exact (nonpivotContractionBlock_entry_same_subset p d W hp hW k a.val b.val
    (a.property.trans b.property.symm)).symm

theorem nonpivotSubsetBlock_det_eligible (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (s : Finset (Fin n)) :
    (nonpivotSubsetBlock p d W hp hW k s).det = (eligibleSubsetBlock p d W k s).det := by
  have he := congrArg Matrix.det (eligibleSubsetBlock_reindex p d W hp hW k s)
  rw [Matrix.det_submatrix_equiv_self] at he
  exact he.symm

end Matrices
end LeanCanny.Algebra.KoszulWeighted

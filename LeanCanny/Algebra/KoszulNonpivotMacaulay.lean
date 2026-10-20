/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulNonpivotRows
public import LeanCanny.Algebra.MacaulayActiveCharacteristic

/-! # Fixed-subset nonpivot blocks are Macaulay principal submatrices

Multiplication by the exterior coordinate powers sends a monomial/exterior
index to its total multidegree. On a fixed exterior subset this map is
injective, and the projected nonpivot contraction has exactly the entries
of the corresponding principal submatrix of the active Macaulay matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def canonicalProductIndex (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k) :
    Macaulay.activeIndices d W := by
  let t := FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1
  have ht : t.degree = Macaulay.level d := canonical_multidegree d W k a
  have hb (i : Fin n) : t i < 2 ^ W := ((Finsupp.le_degree i t).trans_eq ht).trans_lt hW
  refine ⟨FixedWidthPolynomial.index n W t hb, ?_⟩
  rw [Macaulay.mem_activeIndices, FixedWidthPolynomial.vector_index]
  exact ht

theorem vector_canonicalProductIndex (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k) :
    FixedWidthPolynomial.vector n W (canonicalProductIndex d W hW k a).val =
      FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1 :=
  FixedWidthPolynomial.vector_index n W _ _

theorem canonicalProductIndex_injective_on_subset (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a b : CanonicalIndex d (Macaulay.level d) W k)
    (hs : a.1 = b.1) (he : canonicalProductIndex d W hW k a = canonicalProductIndex d W hW k b) : a = b := by
  apply canonicalEmbedding_injective d (Macaulay.level d) W k
  apply Prod.ext
  · have ht := congrArg (fun r : Macaulay.activeIndices d W => FixedWidthPolynomial.vector n W r.val) he
    rw [vector_canonicalProductIndex, vector_canonicalProductIndex] at ht
    have hu : FixedWidthPolynomial.vector n W a.2.val + subsetExponent d b.1 =
        FixedWidthPolynomial.vector n W b.2.val + subsetExponent d b.1 := by
      simpa only [hs] using ht
    exact add_right_cancel hu
  · exact hs

theorem pivot_canonicalProductIndex (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k) :
    Macaulay.pivot d (FixedWidthPolynomial.vector n W (canonicalProductIndex d W hW k a).val)
      ((Macaulay.mem_activeIndices d W _).mp (canonicalProductIndex d W hW k a).property) =
        canonicalPivot d W k a := by
  simp only [vector_canonicalProductIndex, canonicalPivot]

theorem remainder_canonicalProductIndex (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k)
    (ha : ¬HasPivot d W k a) :
    Macaulay.remainder d (FixedWidthPolynomial.vector n W (canonicalProductIndex d W hW k a).val)
      ((Macaulay.mem_activeIndices d W _).mp (canonicalProductIndex d W hW k a).property) =
        (FixedWidthPolynomial.vector n W a.2.val -
          Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a))) + subsetExponent d a.1 := by
  unfold Macaulay.remainder
  rw [pivot_canonicalProductIndex, vector_canonicalProductIndex]
  calc
    _ = (subsetExponent d a.1 + FixedWidthPolynomial.vector n W a.2.val) -
        Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a)) := by
      rw [add_comm (FixedWidthPolynomial.vector n W a.2.val) (subsetExponent d a.1)]
    _ = subsetExponent d a.1 + (FixedWidthPolynomial.vector n W a.2.val -
        Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a))) :=
      add_tsub_assoc_of_le (nonpivot_pivot_divides d W k a ha) (subsetExponent d a.1)
    _ = _ := add_comm _ _

theorem rowPolynomial_canonicalProductIndex (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k)
    (ha : ¬HasPivot d W k a) :
    Macaulay.rowPolynomial p d W (canonicalProductIndex d W hW k a).val
      ((Macaulay.mem_activeIndices d W _).mp (canonicalProductIndex d W hW k a).property) =
        MvPolynomial.monomial (subsetExponent d a.1) (1 : R) *
          (MvPolynomial.monomial (FixedWidthPolynomial.vector n W a.2.val -
            Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a))) 1 * p (canonicalPivot d W k a)) := by
  rw [Macaulay.rowPolynomial, pivot_canonicalProductIndex, remainder_canonicalProductIndex d W hW k a ha,
    ← mul_assoc, MvPolynomial.monomial_mul_monomial, one_mul]
  rw [add_comm (FixedWidthPolynomial.vector n W a.2.val -
    Finsupp.single (canonicalPivot d W k a) (d (canonicalPivot d W k a))) (subsetExponent d a.1)]

theorem nonpivotContractionBlock_entry_same_subset (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a b : {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // ¬HasPivot d W (k + 1) a})
    (hs : a.val.1 = b.val.1) :
    nonpivotContractionBlock p d W hp hW k a b =
      Macaulay.activeMinor p d W (canonicalProductIndex d W hW (k + 1) a.val)
        (canonicalProductIndex d W hW (k + 1) b.val) := by
  have hi : canonicalPivot d W (k + 1) a.val ∉ b.val.1 := by
    have hna : canonicalPivot d W (k + 1) a.val ∉ a.val.1 := a.property
    simpa only [hs] using hna
  rw [nonpivotContractionBlock_entry_of_pivot_not_mem p d W hp hW k a b hi, ite_eq_left hs]
  change _ = Macaulay.matrix p d W (canonicalProductIndex d W hW (k + 1) a.val).val
    (canonicalProductIndex d W hW (k + 1) b.val).val
  rw [Macaulay.matrix, dite_eq_left ((Macaulay.mem_activeIndices d W _).mp
    (canonicalProductIndex d W hW (k + 1) a.val).property),
    rowPolynomial_canonicalProductIndex p d W hW (k + 1) a.val a.property, vector_canonicalProductIndex]
  have ht : FixedWidthPolynomial.vector n W b.val.2.val + subsetExponent d b.val.1 =
      subsetExponent d a.val.1 + FixedWidthPolynomial.vector n W b.val.2.val := by
    rw [hs]
    exact add_comm _ _
  rw [ht, MvPolynomial.coeff_monomial_mul, one_mul]

abbrev NonpivotSubsetIndex (d : Fin n → ℕ) (W k : ℕ) (s : Finset (Fin n)) :=
  {a : {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // ¬HasPivot d W (k + 1) a} // a.val.1 = s}

noncomputable def nonpivotSubsetBlock (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (s : Finset (Fin n)) :=
  (nonpivotContractionBlock p d W hp hW k).submatrix
    (fun a : NonpivotSubsetIndex d W k s => a.val) (fun a : NonpivotSubsetIndex d W k s => a.val)

theorem nonpivotSubsetBlock_macaulay (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (s : Finset (Fin n)) :
    nonpivotSubsetBlock p d W hp hW k s = (Macaulay.activeMinor p d W).submatrix
      (fun a : NonpivotSubsetIndex d W k s => canonicalProductIndex d W hW (k + 1) a.val.val)
      (fun a : NonpivotSubsetIndex d W k s => canonicalProductIndex d W hW (k + 1) a.val.val) := by
  ext a b
  exact nonpivotContractionBlock_entry_same_subset p d W hp hW k a.val b.val (a.property.trans b.property.symm)

theorem nonpivotSubset_productIndex_injective (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) (s : Finset (Fin n)) :
    Function.Injective (fun a : NonpivotSubsetIndex d W k s => canonicalProductIndex d W hW (k + 1) a.val.val) := by
  intro a b he
  apply Subtype.ext
  apply Subtype.ext
  exact canonicalProductIndex_injective_on_subset d W hW (k + 1) a.val.val b.val.val
    (a.property.trans b.property.symm) he

end LeanCanny.Algebra.KoszulWeighted

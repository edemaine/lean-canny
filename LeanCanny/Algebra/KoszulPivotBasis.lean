/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulHomotopySplit
public import LeanCanny.Algebra.KoszulWeightedBasis
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # The monomial summand selected by the normalized homotopy

A canonical monomial/exterior basis vector has a distinguished coordinate:
the Macaulay pivot of its multidegree. The vectors containing this pivot
span exactly the incoming homotopy image. The remaining basis vectors give
a monomial complement over the original commutative coefficient ring.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem canonical_multidegree (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) :
    (FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1).degree = Macaulay.level d := by
  rw [map_add]
  have he : (subsetExponent d a.1).degree = subsetWeight d a.1 := by
    simp only [subsetExponent, map_sum, Finsupp.degree_single, subsetWeight]
  rw [he]
  exact ((mem_canonicalIndices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property).2

noncomputable def canonicalPivot (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) : Fin n :=
  Macaulay.pivot d (FixedWidthPolynomial.vector n W a.2.val + subsetExponent d a.1)
    (canonical_multidegree d W k a)

def HasPivot (d : Fin n → ℕ) (W k : ℕ) (a : CanonicalIndex d (Macaulay.level d) W k) : Prop :=
  canonicalPivot d W k a ∈ a.1

noncomputable def pivotSpan (d : Fin n → ℕ) (W k : ℕ) :
    Submodule R (space (R := R) d (Macaulay.level d) W k) :=
  Submodule.span R ((canonicalBasis (R := R) d (Macaulay.level d) W k) '' {a | HasPivot d W k a})

noncomputable def nonpivotSpan (d : Fin n → ℕ) (W k : ℕ) :
    Submodule R (space (R := R) d (Macaulay.level d) W k) :=
  Submodule.span R ((canonicalBasis (R := R) d (Macaulay.level d) W k) '' {a | ¬HasPivot d W k a})

theorem pivot_nonpivot_isCompl (d : Fin n → ℕ) (W k : ℕ) :
    IsCompl (pivotSpan (R := R) d W k) (nonpivotSpan (R := R) d W k) :=
  (canonicalBasis (R := R) d (Macaulay.level d) W k).linearIndependent.isCompl_span_image
    (canonicalBasis (R := R) d (Macaulay.level d) W k).span_eq (isCompl_compl)

theorem levelHomotopy_canonicalGenerator_eq_zero (d : Fin n → ℕ) (W k : ℕ)
    (a : CanonicalIndex d (Macaulay.level d) W k) (ha : HasPivot d W k a) :
    levelHomotopy (R := R) d (canonicalGenerator (R := R) d (Macaulay.level d) W k a) = 0 := by
  have hs := ((mem_canonicalIndices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property).1
  have hi : canonicalPivot d W k a ∈ Set.range (a.1.orderEmbOfFin hs) := by
    rw [Finset.range_orderEmbOfFin]
    exact ha
  change levelHomotopy (R := R) d
    (ambientBasis (R := R) (FixedWidthPolynomial.vector n W a.2.val, a.1)) = 0
  rw [levelHomotopy_ambientBasis, dite_eq_left (canonical_multidegree d W k a)]
  change powerHomotopy (R := R) d (canonicalPivot d W k a) _ = 0
  rw [ambientBasis_apply, exteriorBasis_as_blade a.1 hs]
  change powerHomotopy (R := R) d (canonicalPivot d W k a)
    (monomialBlade (R := R) (a.1.orderEmbOfFin hs) _) = 0
  rw [powerHomotopy_apply, ← divide_wedge, wedge_word_eq_zero_of_mem _ _ _ hi, map_zero]

theorem pivotSpan_le_homotopy_kernel (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    pivotSpan (R := R) d W k ≤ LinearMap.ker (weightedHomotopy (R := R) d W hW k) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ha, rfl⟩
  apply Subtype.ext
  change levelHomotopy (R := R) d (canonicalBasis (R := R) d (Macaulay.level d) W k a : Total n R) = 0
  rw [canonicalBasis_apply]
  exact levelHomotopy_canonicalGenerator_eq_zero d W k a ha

theorem monomialBlade_mem_pivotSpan (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (v : Fin k → Fin n) (m : Fin n →₀ ℕ)
    (hm : m.degree + wordWeight d v = Macaulay.level d)
    (ht : (m + wordExponent d v).degree = Macaulay.level d)
    (hi : Macaulay.pivot d (m + wordExponent d v) ht ∈ Set.range v) :
    (⟨monomialBlade (R := R) v m, monomialBlade_mem d _ W k hW v m hm⟩ :
      space (R := R) d (Macaulay.level d) W k) ∈ pivotSpan (R := R) d W k := by
  by_cases hv : Function.Injective v
  · have hb (i : Fin n) : m i < 2 ^ W :=
      (Finsupp.le_degree i m).trans_lt ((by omega : m.degree ≤ Macaulay.level d).trans_lt hW)
    let r := FixedWidthPolynomial.index n W m hb
    let s := Finset.univ.image v
    have hr : r ∈ canonicalIndices d (Macaulay.level d) W k s := by
      rw [mem_canonicalIndices, FixedWidthPolynomial.vector_index]
      exact ⟨image_card_of_injective v hv, by rw [subsetWeight_image d v hv]; exact hm⟩
    let a : CanonicalIndex d (Macaulay.level d) W k := ⟨s, r, hr⟩
    have ha : HasPivot d W k a := by
      change Macaulay.pivot d (FixedWidthPolynomial.vector n W r + subsetExponent d s) _ ∈ s
      simp only [r, FixedWidthPolynomial.vector_index, s, wordExponent_image d v hv]
      obtain ⟨j, hj⟩ := hi
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    have hcan : canonicalBasis (R := R) d (Macaulay.level d) W k a ∈ pivotSpan (R := R) d W k :=
      Submodule.subset_span ⟨a, ha, rfl⟩
    have he : canonicalBasis (R := R) d (Macaulay.level d) W k a =
        ((sortPermutation v hv).sign : R) •
          (⟨monomialBlade (R := R) v m, monomialBlade_mem d _ W k hW v m hm⟩ :
            space (R := R) d (Macaulay.level d) W k) := by
      apply Subtype.ext
      rw [canonicalBasis_apply]
      change ambientBasis (R := R) (FixedWidthPolynomial.vector n W r, s) = _
      rw [FixedWidthPolynomial.vector_index]
      exact (monomialBlade_sorted v hv m).symm.trans (monomialBlade_perm v m (sortPermutation v hv))
    rw [he] at hcan
    exact (Submodule.smul_mem_iff_of_isUnit _
      (IsUnit.map (Int.castRingHom R) (sortPermutation v hv).sign.isUnit)).mp hcan
  · have hz : (⟨monomialBlade (R := R) v m, monomialBlade_mem d _ W k hW v m hm⟩ :
        space (R := R) d (Macaulay.level d) W k) = 0 := by
      apply Subtype.ext
      simp only [monomialBlade, blade_eq_zero_of_not_injective v hv, smul_zero, ZeroMemClass.coe_zero]
    rw [hz]
    exact Submodule.zero_mem _

theorem weightedHomotopy_basis_mem_pivotSpan (d : Fin n → ℕ) (W k : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (a : CanonicalIndex d (Macaulay.level d) W k) :
    weightedHomotopy (R := R) d W hW k (canonicalBasis (R := R) d (Macaulay.level d) W k a) ∈
      pivotSpan (R := R) d W (k + 1) := by
  have hs := ((mem_canonicalIndices d (Macaulay.level d) W k a.1 a.2.val).mp a.2.property).1
  let v := a.1.orderEmbOfFin hs
  let m := FixedWidthPolynomial.vector n W a.2.val
  have ht : (m + wordExponent d v).degree = Macaulay.level d := by
    rw [wordExponent_ordered]
    exact canonical_multidegree d W k a
  let i := Macaulay.pivot d (m + wordExponent d v) ht
  have he : (weightedHomotopy (R := R) d W hW k
        (canonicalBasis (R := R) d (Macaulay.level d) W k a) : Total n R) =
      if Finsupp.single i (d i) ≤ m then
        monomialBlade (R := R) (Fin.cons i v) (m - Finsupp.single i (d i)) else 0 := by
    change levelHomotopy (R := R) d (canonicalBasis (R := R) d (Macaulay.level d) W k a : Total n R) = _
    rw [canonicalBasis_apply, canonicalGenerator_apply, exteriorBasis_as_blade a.1 hs]
    change levelHomotopy (R := R) d (monomialBlade (R := R) v m) = _
    rw [levelHomotopy_word d v m ht, powerHomotopy_apply, divide_monomialBlade]
    split_ifs
    · exact wedge_monomialBlade _ _ _
    · exact map_zero _
  by_cases hdiv : Finsupp.single i (d i) ≤ m
  · have hm : m - Finsupp.single i (d i) + wordExponent d (Fin.cons i v) = m + wordExponent d v := by
      rw [wordExponent_cons, ← add_assoc, tsub_add_cancel_of_le hdiv]
    have hwt : (m - Finsupp.single i (d i)).degree + wordWeight d (Fin.cons i v) = Macaulay.level d := by
      rw [← wordExponent_degree, ← map_add, hm]
      exact ht
    have htt : (m - Finsupp.single i (d i) + wordExponent d (Fin.cons i v)).degree = Macaulay.level d := by
      rw [hm]
      exact ht
    have hi : Macaulay.pivot d (m - Finsupp.single i (d i) + wordExponent d (Fin.cons i v)) htt ∈
        Set.range (Fin.cons i v) := by
      simp only [hm]
      exact ⟨0, rfl⟩
    have hmem := monomialBlade_mem_pivotSpan (R := R) d W (k + 1) hW (Fin.cons i v)
      (m - Finsupp.single i (d i)) hwt htt hi
    have hx : weightedHomotopy (R := R) d W hW k (canonicalBasis (R := R) d (Macaulay.level d) W k a) =
        ⟨monomialBlade (R := R) (Fin.cons i v) (m - Finsupp.single i (d i)),
          monomialBlade_mem d _ W (k + 1) hW _ _ hwt⟩ := by
      apply Subtype.ext
      exact he.trans (ite_eq_left hdiv)
    rw [hx]
    exact hmem
  · have hx : weightedHomotopy (R := R) d W hW k (canonicalBasis (R := R) d (Macaulay.level d) W k a) = 0 := by
      apply Subtype.ext
      exact he.trans (ite_eq_right hdiv)
    rw [hx]
    exact Submodule.zero_mem _

theorem homotopy_range_le_pivotSpan (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.range (weightedHomotopy (R := R) d W hW k) ≤ pivotSpan (R := R) d W (k + 1) := by
  have hle : (⊤ : Submodule R (space (R := R) d (Macaulay.level d) W k)) ≤
      (pivotSpan (R := R) d W (k + 1)).comap (weightedHomotopy (R := R) d W hW k) := by
    rw [← (canonicalBasis (R := R) d (Macaulay.level d) W k).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact weightedHomotopy_basis_mem_pivotSpan d W k hW a
  rintro _ ⟨x, rfl⟩
  exact hle (Submodule.mem_top)

theorem homotopy_range_eq_pivotSpan (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    LinearMap.range (weightedHomotopy (R := R) d W hW k) = pivotSpan (R := R) d W (k + 1) := by
  apply le_antisymm (homotopy_range_le_pivotSpan d W hW k)
  rw [← weightedHomotopy_exact d W hW k]
  exact pivotSpan_le_homotopy_kernel d W hW (k + 1)

theorem homotopy_nonpivot_isCompl (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    IsCompl (LinearMap.range (weightedHomotopy (R := R) d W hW k)) (nonpivotSpan (R := R) d W (k + 1)) := by
  rw [homotopy_range_eq_pivotSpan]
  exact pivot_nonpivot_isCompl d W (k + 1)

noncomputable def monomialPieceSplit (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    (LinearMap.range (weightedHomotopy (R := R) d W hW k) × nonpivotSpan (R := R) d W (k + 1)) ≃ₗ[R]
      space (R := R) d (Macaulay.level d) W (k + 1) :=
  Submodule.prodEquivOfIsCompl _ _ (homotopy_nonpivot_isCompl d W hW k)

theorem range_restricted_basis (d : Fin n → ℕ) (W k : ℕ)
    (s : Set (CanonicalIndex d (Macaulay.level d) W k)) :
    Set.range (fun a : s => canonicalBasis (R := R) d (Macaulay.level d) W k a.val) =
      (canonicalBasis (R := R) d (Macaulay.level d) W k) '' s := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, a.property, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

noncomputable def monomialSubsetBasis (d : Fin n → ℕ) (W k : ℕ)
    (s : Set (CanonicalIndex d (Macaulay.level d) W k)) :
    Module.Basis s R (Submodule.span R ((canonicalBasis (R := R) d (Macaulay.level d) W k) '' s)) :=
  (Module.Basis.span ((canonicalBasis (R := R) d (Macaulay.level d) W k).linearIndependent.comp
    (fun a : s => a.val) Subtype.val_injective)).map
      (LinearEquiv.ofEq _ _ (congrArg (Submodule.span R) (range_restricted_basis d W k s)))

theorem monomialSubsetBasis_apply (d : Fin n → ℕ) (W k : ℕ)
    (s : Set (CanonicalIndex d (Macaulay.level d) W k)) (a : s) :
    (monomialSubsetBasis (R := R) d W k s a : space (R := R) d (Macaulay.level d) W k) =
      canonicalBasis (R := R) d (Macaulay.level d) W k a.val := by
  change ((Module.Basis.span ((canonicalBasis (R := R) d (Macaulay.level d) W k).linearIndependent.comp
    (fun a : s => a.val) Subtype.val_injective)) a : space (R := R) d (Macaulay.level d) W k) = _
  exact Module.Basis.coe_span_apply _ a

noncomputable def pivotBasis (d : Fin n → ℕ) (W k : ℕ) :
    Module.Basis {a : CanonicalIndex d (Macaulay.level d) W k // HasPivot d W k a} R (pivotSpan (R := R) d W k) :=
  monomialSubsetBasis d W k {a | HasPivot d W k a}

noncomputable def nonpivotBasis (d : Fin n → ℕ) (W k : ℕ) :
    Module.Basis {a : CanonicalIndex d (Macaulay.level d) W k // ¬HasPivot d W k a} R (nonpivotSpan (R := R) d W k) :=
  monomialSubsetBasis d W k {a | ¬HasPivot d W k a}

noncomputable def homotopyRangeBasis (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ) :
    Module.Basis {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // HasPivot d W (k + 1) a} R
      (LinearMap.range (weightedHomotopy (R := R) d W hW k)) :=
  (pivotBasis d W (k + 1)).map (LinearEquiv.ofEq _ _ (homotopy_range_eq_pivotSpan d W hW k).symm)

theorem homotopyRangeBasis_apply (d : Fin n → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (k : ℕ)
    (a : {a : CanonicalIndex d (Macaulay.level d) W (k + 1) // HasPivot d W (k + 1) a}) :
    (homotopyRangeBasis (R := R) d W hW k a : space (R := R) d (Macaulay.level d) W (k + 1)) =
      canonicalBasis (R := R) d (Macaulay.level d) W (k + 1) a.val := by
  change (pivotBasis (R := R) d W (k + 1) a : space (R := R) d (Macaulay.level d) W (k + 1)) = _
  exact monomialSubsetBasis_apply d W (k + 1) _ a

end LeanCanny.Algebra.KoszulWeighted

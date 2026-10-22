/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayRelationMinor

/-! # Triangular blocks of the relation and extraneous matrices

The complementary Koszul relation matrix is lower block triangular by its
input coordinate. The extraneous Macaulay matrix is upper block triangular
by the greatest eligible coordinate of its monomial.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

theorem productExponent_self_le (d : Fin n → ℕ) (W : ℕ) (a : MultiplierIndex d W) :
    d a.1 ≤ productExponent d W a a.1 := by
  simp only [productExponent, Finsupp.add_apply, Finsupp.single_eq_same]
  exact Nat.le_add_left _ _

theorem divisionPivot_lt (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a : RelationIndex d W) :
    (divisionRow d W hW a.val).1 < a.val.1 := by
  have hne : a.val.1 ≠ (divisionRow d W hW a.val).1 := by
    intro h
    have ht := selectedMultiplier_add d W (productIndex d W hW a.val)
    rw [vector_productIndex] at ht
    have he := multiplierIndex_ext d W a.val (divisionRow d W hW a.val) h ht.symm
    exact a.property ⟨productIndex d W hW a.val, he.symm⟩
  have hi : a.val.1 ∈ eligible d (FixedWidthPolynomial.vector n W (productIndex d W hW a.val).val) := by
    rw [vector_productIndex]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact productExponent_self_le d W a.val
  have hle : (divisionRow d W hW a.val).1 ≤ a.val.1 :=
    Finset.min'_le _ _ hi
  exact lt_of_le_of_ne hle (Ne.symm hne)

theorem relationMinor_zero_of_component_lt (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a b : RelationIndex d W)
    (hab : a.val.1 < b.val.1) : relationMinor p d W hW a b = 0 := by
  have hj := divisionPivot_lt d W hW a
  have hba : b.val.1 ≠ a.val.1 := ne_of_gt hab
  have hbj : b.val.1 ≠ (divisionRow d W hW a.val).1 := ne_of_gt (hj.trans hab)
  change divisionRelations p d W hW a.val b.val = 0
  rw [divisionRelations, ite_eq_right (ne_of_gt hj)]
  change (koszulMultipliers p a.val.1 (divisionRow d W hW a.val).1 (divisionExponent d W hW a.val) b.val.1).coeff
    (FixedWidthPolynomial.vector n W b.val.2.val) = 0
  simp only [koszulMultipliers, Pi.sub_apply, Pi.single_eq_of_ne hba, Pi.single_eq_of_ne hbj, sub_self]
  simp

theorem relationMinor_blockTriangular (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    (relationMinor p d W hW).BlockTriangular (fun a => OrderDual.toDual a.val.1) := by
  intro a b hab
  exact relationMinor_zero_of_component_lt p d W hW a b hab

noncomputable def lastEligible (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) : Fin n :=
  (eligible d e).max' (eligible_nonempty d e he)

theorem lastEligible_mem (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    lastEligible d e he ∈ eligible d e := Finset.max'_mem _ _

theorem le_lastEligible (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d)
    (i : Fin n) (hi : d i ≤ e i) : i ≤ lastEligible d e he := by
  exact Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem lastEligible_eligible (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d) :
    d (lastEligible d e he) ≤ e (lastEligible d e he) :=
  (Finset.mem_filter.mp (lastEligible_mem d e he)).2

theorem pivot_lt_lastEligible (d : Fin n → ℕ) (e : Fin n →₀ ℕ) (he : e.degree = level d)
    (hu : Unreduced d e) : pivot d e he < lastEligible d e he :=
  Finset.min'_lt_max'_of_card (eligible d e) hu

noncomputable def extraneousLast (d : Fin n → ℕ) (W : ℕ) (r : extraneousIndices d W) : Fin n :=
  lastEligible d (FixedWidthPolynomial.vector n W r.val) ((mem_extraneousIndices d W r.val).mp r.property).1

theorem extraneousMinor_blockTriangular (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) :
    (extraneousMinor p d W).BlockTriangular (extraneousLast d W) := by
  intro r s hrs
  have hr := (mem_extraneousIndices d W r.val).mp r.property
  have hs := (mem_extraneousIndices d W s.val).mp s.property
  have hj := pivot_lt_lastEligible d _ hr.1 hr.2
  have hd := lastEligible_eligible d _ hr.1
  change pivot d (FixedWidthPolynomial.vector n W r.val) hr.1 < extraneousLast d W r at hj
  change d (extraneousLast d W r) ≤ FixedWidthPolynomial.vector n W r.val (extraneousLast d W r) at hd
  have hn : ¬remainder d (FixedWidthPolynomial.vector n W r.val) hr.1 ≤ FixedWidthPolynomial.vector n W s.val := by
    intro hle
    have hrem : remainder d (FixedWidthPolynomial.vector n W r.val) hr.1 (extraneousLast d W r) =
        FixedWidthPolynomial.vector n W r.val (extraneousLast d W r) := by
      simp only [remainder, Finsupp.tsub_apply, Finsupp.single_eq_of_ne (ne_of_gt hj), Nat.sub_zero]
    have hterm := hle (extraneousLast d W r)
    rw [hrem] at hterm
    have hmax := le_lastEligible d (FixedWidthPolynomial.vector n W s.val) hs.1
      (extraneousLast d W r) (hd.trans hterm)
    exact (not_le_of_gt hrs) hmax
  change matrix p d W r.val s.val = 0
  rw [entry_active p d W r.val s.val hr.1, ite_eq_right hn]

noncomputable def relationProduct (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a : RelationIndex d W) : extraneousIndices d W := by
  let r := productIndex d W hW a.val
  have hr := (mem_activeIndices d W r.val).mp r.property
  refine ⟨r.val, (mem_extraneousIndices d W r.val).mpr ⟨hr, ?_⟩⟩
  apply (unreduced_iff d _).mpr
  refine ⟨a.val.1, (divisionRow d W hW a.val).1, ne_of_gt (divisionPivot_lt d W hW a), ?_, ?_⟩
  · rw [show FixedWidthPolynomial.vector n W r.val = productExponent d W a.val from vector_productIndex d W hW a.val]
    exact productExponent_self_le d W a.val
  · exact pivot_le d _ hr

theorem vector_relationProduct (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a : RelationIndex d W) :
    FixedWidthPolynomial.vector n W (relationProduct d W hW a).val = productExponent d W a.val :=
  vector_productIndex d W hW a.val

noncomputable def relationLast (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a : RelationIndex d W) : Fin n :=
  extraneousLast d W (relationProduct d W hW a)

theorem component_le_relationLast (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a : RelationIndex d W) :
    a.val.1 ≤ relationLast d W hW a := by
  exact le_lastEligible d _ ((mem_extraneousIndices d W _).mp (relationProduct d W hW a).property).1 a.val.1
    (by rw [vector_relationProduct]; exact productExponent_self_le d W a.val)

theorem relationProduct_injective_of_component_eq (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W)
    (a b : RelationIndex d W) (hi : a.val.1 = b.val.1)
    (h : relationProduct d W hW a = relationProduct d W hW b) : a = b := by
  apply Subtype.ext
  apply multiplierIndex_ext d W a.val b.val hi
  have hv := congrArg (fun r : extraneousIndices d W => FixedWidthPolynomial.vector n W r.val) h
  simpa only [vector_relationProduct] using hv

theorem coeff_monomial_mul_translate (p : MvPolynomial (Fin n) R) (a b c : Fin n →₀ ℕ) :
    (MvPolynomial.monomial (a + c) 1 * p).coeff (b + c) = (MvPolynomial.monomial a 1 * p).coeff b := by
  simp only [MvPolynomial.coeff_monomial_mul', add_le_add_iff_right, add_tsub_add_eq_tsub_right]

theorem relationMinor_same_component (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a b : RelationIndex d W)
    (hi : a.val.1 = b.val.1) :
    relationMinor p d W hW a b = extraneousMinor p d W (relationProduct d W hW a) (relationProduct d W hW b) := by
  have hj := divisionPivot_lt d W hW a
  have haj : a.val.1 ≠ (divisionRow d W hW a.val).1 := ne_of_gt hj
  have hbj : b.val.1 ≠ (divisionRow d W hW a.val).1 := hi ▸ haj
  have hq : koszulMultipliers p a.val.1 (divisionRow d W hW a.val).1 (divisionExponent d W hW a.val) b.val.1 =
      MvPolynomial.monomial (divisionExponent d W hW a.val) 1 * p (divisionRow d W hW a.val).1 := by
    simp only [koszulMultipliers, Pi.sub_apply, Pi.single_apply, ite_eq_left hi.symm, ite_eq_right hbj, sub_zero]
  change divisionRelations p d W hW a.val b.val = matrix p d W
    (productIndex d W hW a.val).val (productIndex d W hW b.val).val
  rw [divisionRelations, ite_eq_right haj]
  change (koszulMultipliers p a.val.1 (divisionRow d W hW a.val).1 (divisionExponent d W hW a.val) b.val.1).coeff
    (FixedWidthPolynomial.vector n W b.val.2.val) = _
  rw [hq, matrix, dite_eq_left ((mem_activeIndices d W _).mp (productIndex d W hW a.val).property),
    ← sourceRow_selected]
  change (MvPolynomial.monomial (divisionExponent d W hW a.val) 1 * p (divisionRow d W hW a.val).1).coeff
      (FixedWidthPolynomial.vector n W b.val.2.val) =
    (MvPolynomial.monomial (FixedWidthPolynomial.vector n W (divisionRow d W hW a.val).2.val) 1 *
      p (divisionRow d W hW a.val).1).coeff (FixedWidthPolynomial.vector n W (productIndex d W hW b.val).val)
  rw [← divisionExponent_add_original d W hW a.val haj, vector_productIndex]
  have hb : productExponent d W b.val = FixedWidthPolynomial.vector n W b.val.2.val +
      Finsupp.single a.val.1 (d a.val.1) :=
    congrArg (fun i : Fin n => FixedWidthPolynomial.vector n W b.val.2.val + Finsupp.single i (d i)) hi.symm
  rw [hb]
  exact (coeff_monomial_mul_translate _ _ _ _).symm

theorem relationMinor_same_component_zero_of_last_lt (p : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (a b : RelationIndex d W)
    (hi : a.val.1 = b.val.1) (hl : relationLast d W hW b < relationLast d W hW a) :
    relationMinor p d W hW a b = 0 := by
  rw [relationMinor_same_component p d W hW a b hi]
  exact extraneousMinor_blockTriangular p d W hl

noncomputable def multiplierAt (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W)
    (i : Fin n) (hi : d i ≤ FixedWidthPolynomial.vector n W r.val i) : MultiplierIndex d W := by
  let m := FixedWidthPolynomial.vector n W r.val - Finsupp.single i (d i)
  have hb (j : Fin n) : m j < 2 ^ W :=
    (Nat.sub_le _ _).trans_lt (FixedWidthPolynomial.vector_lt n W r.val j)
  have he : m + Finsupp.single i (d i) = FixedWidthPolynomial.vector n W r.val :=
    tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
  refine ⟨i, FixedWidthPolynomial.index n W m hb, ?_⟩
  rw [mem_multiplierIndices, FixedWidthPolynomial.vector_index]
  have hg := congrArg Finsupp.degree he
  simpa only [map_add, Finsupp.degree_single, (mem_activeIndices d W r.val).mp r.property] using hg

theorem multiplierAt_fst (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W)
    (i : Fin n) (hi : d i ≤ FixedWidthPolynomial.vector n W r.val i) : (multiplierAt d W r i hi).1 = i := rfl

theorem productExponent_multiplierAt (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W)
    (i : Fin n) (hi : d i ≤ FixedWidthPolynomial.vector n W r.val i) :
    productExponent d W (multiplierAt d W r i hi) = FixedWidthPolynomial.vector n W r.val := by
  let m := FixedWidthPolynomial.vector n W r.val - Finsupp.single i (d i)
  have hb (j : Fin n) : m j < 2 ^ W := by
    change (FixedWidthPolynomial.vector n W r.val - Finsupp.single i (d i)) j < 2 ^ W
    rw [Finsupp.tsub_apply]
    exact (Nat.sub_le _ _).trans_lt (FixedWidthPolynomial.vector_lt n W r.val j)
  have he : FixedWidthPolynomial.vector n W (multiplierAt d W r i hi).2.val = m :=
    FixedWidthPolynomial.vector_index n W m hb
  exact (congrArg (fun e : Fin n →₀ ℕ => e + Finsupp.single i (d i)) he).trans
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi))

theorem productIndex_multiplierAt (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) (r : activeIndices d W)
    (i : Fin n) (hi : d i ≤ FixedWidthPolynomial.vector n W r.val i) :
    productIndex d W hW (multiplierAt d W r i hi) = r := by
  apply Subtype.ext
  apply FixedWidthPolynomial.vector_injective n W
  rw [vector_productIndex, productExponent_multiplierAt]

end LeanCanny.Algebra.Macaulay

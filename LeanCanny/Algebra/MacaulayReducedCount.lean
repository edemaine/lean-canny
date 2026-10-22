/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayActiveCharacteristic

/-! # Counting the reduced monomials at the Macaulay level

A reduced monomial has exactly one eligible coordinate. For that coordinate i,
the other exponents range independently below their degrees, and the level
determines the exponent at i. This gives the sum of products excluding i.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ}

abbrev ReducedBox (d : Fin n → ℕ) (i : Fin n) := (j : Fin n) → Fin (if j = i then 1 else d j)

def otherSum (i : Fin n) (a : Fin n → ℕ) : ℕ := ∑ j ∈ Finset.univ.erase i, a j

noncomputable def reducedExponent (d : Fin n → ℕ) (i : Fin n) (a : ReducedBox d i) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => if j = i then level d - otherSum i (fun k => (a k).val) else (a j).val)

theorem reducedExponent_apply (d : Fin n → ℕ) (i : Fin n) (a : ReducedBox d i) (j : Fin n) :
    reducedExponent d i a j = if j = i then level d - otherSum i (fun k => (a k).val) else (a j).val := rfl

theorem level_eq_otherSum (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) :
    level d = d i + otherSum i (fun j => d j - 1) := by
  have h := Finset.sum_erase_add Finset.univ (fun j => d j - 1) (Finset.mem_univ i)
  unfold level otherSum
  rw [← h, Nat.add_assoc, Nat.sub_add_cancel (hd i), Nat.add_comm]

theorem box_other_lt (d : Fin n → ℕ) (i : Fin n) (a : ReducedBox d i) (j : Fin n) (hji : j ≠ i) :
    (a j).val < d j := by
  have h := (a j).isLt
  simpa only [ite_eq_right hji] using h

theorem box_sum_le (d : Fin n → ℕ) (i : Fin n) (a : ReducedBox d i) :
    otherSum i (fun j => (a j).val) ≤ otherSum i (fun j => d j - 1) := by
  apply Finset.sum_le_sum
  intro j hj
  have h := box_other_lt d i a j (Finset.mem_erase.mp hj).1
  omega

theorem reducedExponent_pivot (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) (a : ReducedBox d i) :
    d i ≤ reducedExponent d i a i := by
  rw [reducedExponent_apply, ite_eq_left rfl, level_eq_otherSum d hd i]
  have h := box_sum_le d i a
  omega

theorem reducedExponent_other (d : Fin n → ℕ) (i : Fin n) (a : ReducedBox d i) (j : Fin n) (hji : j ≠ i) :
    reducedExponent d i a j < d j := by
  rw [reducedExponent_apply, ite_eq_right hji]
  exact box_other_lt d i a j hji

theorem reducedExponent_degree (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) (a : ReducedBox d i) :
    (reducedExponent d i a).degree = level d := by
  rw [Finsupp.degree_eq_sum]
  have hs : (∑ j ∈ Finset.univ.erase i, reducedExponent d i a j) = otherSum i (fun j => (a j).val) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_right (Finset.mem_erase.mp hj).1
  have h := Finset.sum_erase_add Finset.univ (reducedExponent d i a) (Finset.mem_univ i)
  rw [hs, reducedExponent_apply, ite_eq_left rfl] at h
  have hle : otherSum i (fun j => (a j).val) ≤ level d :=
    (box_sum_le d i a).trans (by rw [level_eq_otherSum d hd i]; omega)
  omega

theorem card_reducedBox (d : Fin n → ℕ) (i : Fin n) :
    Fintype.card (ReducedBox d i) = ∏ j ∈ Finset.univ.erase i, d j := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  have h := Finset.prod_erase_mul Finset.univ (fun j => if j = i then 1 else d j) (Finset.mem_univ i)
  rw [ite_eq_left rfl, mul_one] at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

theorem reducedExponent_eligible (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) (a : ReducedBox d i) :
    eligible d (reducedExponent d i a) = {i} := by
  ext j
  simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hji
    exact Nat.not_le_of_lt (reducedExponent_other d i a j hji) hj
  · intro hji
    subst j
    exact reducedExponent_pivot d hd i a

noncomputable def reducedRank (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (x : (i : Fin n) × ReducedBox d i) : ↥(activeIndices d W \ extraneousIndices d W) := by
  rcases x with ⟨i, a⟩
  have hb (j : Fin n) : reducedExponent d i a j < 2 ^ W := by
    have h : reducedExponent d i a j ≤ (reducedExponent d i a).degree := by
      rw [Finsupp.degree_eq_sum]
      exact Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    exact (h.trans_eq (reducedExponent_degree d hd i a)).trans_lt hW
  refine ⟨FixedWidthPolynomial.index n W (reducedExponent d i a) hb, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · rw [mem_activeIndices, FixedWidthPolynomial.vector_index]
    exact reducedExponent_degree d hd i a
  · intro hx
    have h := ((mem_extraneousIndices d W _).mp hx).2
    rw [FixedWidthPolynomial.vector_index, Unreduced, reducedExponent_eligible d hd i a, Finset.card_singleton] at h
    omega

theorem reducedRank_vector (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (i : Fin n) (a : ReducedBox d i) :
    FixedWidthPolynomial.vector n W (reducedRank d hd W hW ⟨i, a⟩).val = reducedExponent d i a :=
  FixedWidthPolynomial.vector_index n W _ _

theorem reducedRank_injective (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) :
    Function.Injective (reducedRank d hd W hW) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hv := congrArg (fun r : ↥(activeIndices d W \ extraneousIndices d W) => FixedWidthPolynomial.vector n W r.val) h
  rw [reducedRank_vector, reducedRank_vector] at hv
  have hij : i = j := by
    by_contra hij
    have hl := reducedExponent_other d j b i hij
    rw [← hv] at hl
    exact Nat.not_lt_of_ge (reducedExponent_pivot d hd i a) hl
  subst j
  have hab : a = b := by
    funext k
    apply Fin.ext
    by_cases hki : k = i
    · subst k
      have ha : (a i).val < 1 := (a i).isLt.trans_le (by simp)
      have hb : (b i).val < 1 := (b i).isLt.trans_le (by simp)
      omega
    · have hk := congrArg (fun e : Fin n →₀ ℕ => e k) hv
      simpa only [reducedExponent_apply, ite_eq_right hki] using hk
  cases hab
  rfl

theorem reducedRank_surjective (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) :
    Function.Surjective (reducedRank d hd W hW) := by
  intro r
  let m := FixedWidthPolynomial.vector n W r.val
  have hm : m.degree = level d := (mem_activeIndices d W r.val).mp (Finset.mem_sdiff.mp r.property).1
  have hn : ¬Unreduced d m := by
    intro h
    exact (Finset.mem_sdiff.mp r.property).2 ((mem_extraneousIndices d W r.val).mpr ⟨hm, h⟩)
  obtain ⟨i, hi⟩ := exists_pivot d m hm
  have ho (j : Fin n) (hji : j ≠ i) : m j < d j := by
    by_contra hj
    exact hn ((unreduced_iff d m).mpr ⟨i, j, hji.symm, hi, Nat.le_of_not_gt hj⟩)
  let a : ReducedBox d i := fun j => ⟨if j = i then 0 else m j, by
    by_cases hji : j = i
    · simp only [hji, ite_true, Nat.zero_lt_one]
    · simpa only [ite_eq_right hji] using ho j hji⟩
  have ha : otherSum i (fun j => (a j).val) = otherSum i m := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [a, ite_eq_right (Finset.mem_erase.mp hj).1]
  have hv : reducedExponent d i a = m := by
    ext j
    by_cases hji : j = i
    · subst j
      rw [reducedExponent_apply, ite_eq_left rfl, ha]
      have hs := Finset.sum_erase_add Finset.univ m (Finset.mem_univ i)
      rw [← Finsupp.degree_eq_sum, hm] at hs
      change (∑ j ∈ Finset.univ.erase i, m j) + m i = level d at hs
      unfold otherSum
      omega
    · simp only [reducedExponent_apply, ite_eq_right hji, a]
  refine ⟨⟨i, a⟩, ?_⟩
  apply Subtype.ext
  apply FixedWidthPolynomial.vector_injective n W
  rw [reducedRank_vector]
  exact hv

theorem card_reducedIndices (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) :
    (activeIndices d W \ extraneousIndices d W).card = ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  have h := Fintype.card_congr (Equiv.ofBijective (reducedRank d hd W hW)
    ⟨reducedRank_injective d hd W hW, reducedRank_surjective d hd W hW⟩)
  simpa only [Fintype.card_sigma, Fintype.card_coe, card_reducedBox] using h.symm

theorem card_active_eq_extraneous_add (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) :
    (activeIndices d W).card = (extraneousIndices d W).card + ∑ i, ∏ j ∈ Finset.univ.erase i, d j := by
  have hs := extraneousIndices_subset_active d W
  have hc := Finset.card_sdiff_of_subset hs
  rw [card_reducedIndices d hd W hW] at hc
  have hl := Finset.card_le_card hs
  omega

end LeanCanny.Algebra.Macaulay

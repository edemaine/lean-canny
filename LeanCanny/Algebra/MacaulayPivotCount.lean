/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayReducedCount
public import LeanCanny.Algebra.MacaulayExtraneousLast

/-! # Counting rows that use the last input polynomial

At the last pivot, every active monomial is reduced. Restricting the reduced
monomial bijection to that pivot gives the product of the other degrees.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped BigOperators Classical
variable {n : ℕ}

noncomputable def activePivot (d : Fin n → ℕ) (W : ℕ) (r : activeIndices d W) : Fin n :=
  pivot d (FixedWidthPolynomial.vector n W r.val) ((mem_activeIndices d W r.val).mp r.property)

noncomputable def pivotRows (d : Fin n → ℕ) (W : ℕ) (i : Fin n) : Finset (activeIndices d W) :=
  Finset.univ.filter (fun r => activePivot d W r = i)

theorem mem_pivotRows (d : Fin n → ℕ) (W : ℕ) (i : Fin n) (r : activeIndices d W) :
    r ∈ pivotRows d W i ↔ activePivot d W r = i := by
  simp only [pivotRows, Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def reducedAsActive (d : Fin n → ℕ) (W : ℕ)
    (r : ↥(activeIndices d W \ extraneousIndices d W)) : activeIndices d W :=
  ⟨r.val, (Finset.mem_sdiff.mp r.property).1⟩

theorem reducedAsActive_injective (d : Fin n → ℕ) (W : ℕ) : Function.Injective (reducedAsActive d W) := by
  intro r s h
  exact Subtype.ext (congrArg (fun x : activeIndices d W => x.val) h)

theorem activePivot_reducedRank (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (i : Fin n) (a : ReducedBox d i) :
    activePivot d W (reducedAsActive d W (reducedRank d hd W hW ⟨i, a⟩)) = i := by
  have h := Finset.min'_mem
    (eligible d (FixedWidthPolynomial.vector n W (reducedRank d hd W hW ⟨i, a⟩).val))
    (eligible_nonempty d _ ((mem_activeIndices d W _).mp
      (Finset.mem_sdiff.mp (reducedRank d hd W hW ⟨i, a⟩).property).1))
  have he : eligible d (FixedWidthPolynomial.vector n W (reducedRank d hd W hW ⟨i, a⟩).val) = {i} := by
    rw [reducedRank_vector, reducedExponent_eligible d hd i a]
  change activePivot d W (reducedAsActive d W (reducedRank d hd W hW ⟨i, a⟩)) ∈
    eligible d (FixedWidthPolynomial.vector n W (reducedRank d hd W hW ⟨i, a⟩).val) at h
  rw [he, Finset.mem_singleton] at h
  exact h

noncomputable def pivotRank (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (i : Fin n) (a : ReducedBox d i) : pivotRows d W i :=
  ⟨reducedAsActive d W (reducedRank d hd W hW ⟨i, a⟩),
    (mem_pivotRows d W i _).mpr (activePivot_reducedRank d hd W hW i a)⟩

theorem pivotRank_injective (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W) (i : Fin n) :
    Function.Injective (pivotRank d hd W hW i) := by
  intro a b h
  have hA := congrArg Subtype.val h
  have hR := reducedAsActive_injective d W hA
  exact sigma_mk_injective (reducedRank_injective d hd W hW hR)

theorem pivotRank_surjective_last (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (last : Fin n) (hlast : ∀ j, j ≤ last) : Function.Surjective (pivotRank d hd W hW last) := by
  intro r
  have hp := (mem_pivotRows d W last r.val).mp r.property
  have hn : r.val.val ∉ extraneousIndices d W := by
    intro he
    have ha := (mem_extraneousIndices d W r.val.val).mp he
    exact pivot_ne_last d _ ha.1 ha.2 last hlast hp
  let rr : ↥(activeIndices d W \ extraneousIndices d W) := ⟨r.val.val, Finset.mem_sdiff.mpr ⟨r.val.property, hn⟩⟩
  obtain ⟨⟨i, a⟩, h⟩ := reducedRank_surjective d hd W hW rr
  have hA : reducedAsActive d W (reducedRank d hd W hW ⟨i, a⟩) = r.val :=
    congrArg (reducedAsActive d W) h
  have hP := congrArg (activePivot d W) hA
  rw [activePivot_reducedRank, hp] at hP
  subst i
  exact ⟨a, Subtype.ext hA⟩

theorem card_pivotRows_last (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (last : Fin n) (hlast : ∀ j, j ≤ last) :
    (pivotRows d W last).card = ∏ j ∈ Finset.univ.erase last, d j := by
  have h := Fintype.card_congr (Equiv.ofBijective (pivotRank d hd W hW last)
    ⟨pivotRank_injective d hd W hW last, pivotRank_surjective_last d hd W hW last hlast⟩)
  simpa only [Fintype.card_coe, card_reducedBox] using h.symm

theorem sum_last_pivot_weights (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (W : ℕ) (hW : level d < 2 ^ W)
    (last : Fin n) (hlast : ∀ j, j ≤ last) (E : ℕ) :
    (∑ r : activeIndices d W, if activePivot d W r = last then E else 0) =
      (∏ j ∈ Finset.univ.erase last, d j) * E := by
  rw [← card_pivotRows_last d hd W hW last hlast, ← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul]
  rfl

end LeanCanny.Algebra.Macaulay

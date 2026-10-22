/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FinitePositionMasks

/-! # Selecting coordinates from full finite position masks

Position masks in a common finite ambient type can be decoded in any
sufficiently long decreasing coordinate list. Encoding and decoding are
inverse, preserve cardinality, and omit the least coordinate when every
selected position has at least one coordinate after it.
-/

@[expose] public section

namespace LeanCanny.Algebra.FinitePositionMasks
open scoped Classical
variable {α : Type*} [LinearOrder α] {N : ℕ}

noncomputable def coordinateRank (A : Finset α) (N : ℕ) (hA : A.card ≤ N) (x : A) : Fin N :=
  ⟨(reverseRank A x).val, (reverseRank A x).isLt.trans_le hA⟩

theorem coordinateRank_injective (A : Finset α) (N : ℕ) (hA : A.card ≤ N) :
    Function.Injective (coordinateRank A N hA) := by
  intro x y he
  exact (reverseRank A).injective (Fin.ext (congrArg (fun i : Fin N => i.val) he))

noncomputable def encodePositions (A s : Finset α) (hs : s ⊆ A) (N : ℕ) (hA : A.card ≤ N) : Finset (Fin N) :=
  Finset.univ.image (fun x : s => coordinateRank A N hA ⟨x.val, hs x.property⟩)

theorem encodePositions_bound (A s : Finset α) (hs : s ⊆ A) (N : ℕ) (hA : A.card ≤ N)
    (j : Fin N) (hj : j ∈ encodePositions A s hs N hA) : j.val < A.card := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hj
  exact (reverseRank A ⟨x.val, hs x.property⟩).isLt

noncomputable def positionAt (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (j : m) : α :=
  ((reverseRank A).symm ⟨j.val.val, hb j.val j.property⟩).val

theorem positionAt_mem (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (j : m) : positionAt A m hb j ∈ A :=
  ((reverseRank A).symm ⟨j.val.val, hb j.val j.property⟩).property

theorem positionAt_rank (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (j : m) :
    reverseRank A ⟨positionAt A m hb j, positionAt_mem A m hb j⟩ = ⟨j.val.val, hb j.val j.property⟩ :=
  (reverseRank A).apply_symm_apply _

theorem positionAt_injective (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) : Function.Injective (positionAt A m hb) := by
  intro x y he
  have ha : (⟨positionAt A m hb x, positionAt_mem A m hb x⟩ : A) =
      ⟨positionAt A m hb y, positionAt_mem A m hb y⟩ := Subtype.ext he
  have hr := congrArg (reverseRank A) ha
  rw [positionAt_rank, positionAt_rank] at hr
  exact Subtype.ext (Fin.ext (congrArg (fun i : Fin A.card => i.val) hr))

theorem positionAt_le_of_rank_le (A B : Finset α) (m : Finset (Fin N))
    (hA : ∀ j ∈ m, j.val < A.card) (hB : ∀ j ∈ m, j.val < B.card) (j : m)
    (hc : positionAt A m hA j ∈ B)
    (hr : j.val.val ≤ (reverseRank B ⟨positionAt A m hA j, hc⟩).val) :
    positionAt A m hA j ≤ positionAt B m hB j := by
  by_contra hn
  have hlt := (reverseRank_lt_iff B ⟨positionAt A m hA j, hc⟩
    ⟨positionAt B m hB j, positionAt_mem B m hB j⟩).mpr (lt_of_not_ge hn)
  rw [positionAt_rank] at hlt
  have hnat : (reverseRank B ⟨positionAt A m hA j, hc⟩).val < j.val.val := hlt
  omega

noncomputable def selectPositions (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) : Finset α := Finset.univ.image (positionAt A m hb)

theorem selectPositions_subset (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) : selectPositions A m hb ⊆ A := by
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact positionAt_mem A m hb j

theorem selectPositions_card (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) : (selectPositions A m hb).card = m.card := by
  rw [selectPositions, Finset.card_image_of_injective _ (positionAt_injective A m hb), Finset.card_univ, Fintype.card_coe]

theorem positionAt_coordinateRank (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (hA : A.card ≤ N) (j : m) (x : A)
    (he : j.val = coordinateRank A N hA x) : positionAt A m hb j = x.val := by
  have hr : (⟨j.val.val, hb j.val j.property⟩ : Fin A.card) = reverseRank A x :=
    Fin.ext (congrArg (fun i : Fin N => i.val) he)
  change ((reverseRank A).symm ⟨j.val.val, hb j.val j.property⟩).val = x.val
  rw [hr, Equiv.symm_apply_apply]

theorem encode_selectPositions (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (hA : A.card ≤ N) :
    encodePositions A (selectPositions A m hb) (selectPositions_subset A m hb) N hA = m := by
  ext j
  constructor
  · intro hj
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp x.property
    have hr : reverseRank A ⟨x.val, selectPositions_subset A m hb x.property⟩ =
        ⟨u.val.val, hb u.val u.property⟩ := by
      simpa only [hu] using positionAt_rank A m hb u
    have hv := congrArg Fin.val hx
    have he : j = u.val := Fin.ext (hv.symm.trans (congrArg (fun i : Fin A.card => i.val) hr))
    simpa only [he] using u.property
  · intro hj
    have hx : positionAt A m hb ⟨j, hj⟩ ∈ selectPositions A m hb :=
      Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨⟨positionAt A m hb ⟨j, hj⟩, hx⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    exact congrArg (fun i : Fin A.card => i.val) (positionAt_rank A m hb ⟨j, hj⟩)

theorem select_encodePositions (A s : Finset α) (hs : s ⊆ A) (N : ℕ) (hA : A.card ≤ N) :
    selectPositions A (encodePositions A s hs N hA) (encodePositions_bound A s hs N hA) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp j.property
    have he := positionAt_coordinateRank A (encodePositions A s hs N hA)
      (encodePositions_bound A s hs N hA) hA j ⟨c.val, hs c.property⟩ hc.symm
    have hcx : c.val = x := he.symm.trans hj
    simpa only [hcx] using c.property
  · intro hx
    let j := coordinateRank A N hA ⟨x, hs hx⟩
    have hj : j ∈ encodePositions A s hs N hA := Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
    have he := positionAt_coordinateRank A (encodePositions A s hs N hA)
      (encodePositions_bound A s hs N hA) hA ⟨j, hj⟩ ⟨x, hs hx⟩ rfl
    exact Finset.mem_image.mpr ⟨⟨j, hj⟩, Finset.mem_univ _, he⟩

theorem reverseRank_min_val (A : Finset α) (x : A) (hx : ∀ y ∈ A, x.val ≤ y) :
    (reverseRank A x).val + 1 = A.card := by
  have hf : A.filter (fun y => x.val < y) = A.erase x.val := by
    ext y
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hlt⟩
      exact ⟨ne_of_gt hlt, hy⟩
    · rintro ⟨hne, hy⟩
      exact ⟨hy, lt_of_le_of_ne (hx y hy) (Ne.symm hne)⟩
  rw [reverseRank_val, hf, Finset.card_erase_of_mem x.property]
  have hp : 0 < A.card := Finset.card_pos.mpr ⟨x.val, x.property⟩
  omega

theorem min_not_mem_selectPositions (A : Finset α) (m : Finset (Fin N))
    (hb : ∀ j ∈ m, j.val < A.card) (hm : ∀ j ∈ m, j.val + 2 ≤ A.card)
    (x : A) (hx : ∀ y ∈ A, x.val ≤ y) : x.val ∉ selectPositions A m hb := by
  intro hxmem
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hxmem
  have hr : reverseRank A x = ⟨j.val.val, hb j.val j.property⟩ := by
    simpa only [hj] using positionAt_rank A m hb j
  have hmin := reverseRank_min_val A x hx
  rw [hr] at hmin
  change j.val.val + 1 = A.card at hmin
  have hbound := hm j.val j.property
  omega

end LeanCanny.Algebra.FinitePositionMasks

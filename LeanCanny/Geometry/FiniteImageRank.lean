/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image

/-! # Distinct coordinate ranks by least representatives

A finite list may repeat coordinate values. Selecting the least index for
each value counts its image once. The construction depends only on equality
and order comparisons and is constant when those comparisons are constant.
-/

@[expose] public section
namespace LeanCanny.Geometry.FiniteImageRank
open scoped Classical
variable {α β : Type*} [LinearOrder α] [LinearOrder β]

noncomputable def representatives (s : Finset α) (f : α → β) : Finset α :=
  s.filter (fun i => ∀ j ∈ s, f j = f i → i ≤ j)

theorem representative_exists (s : Finset α) (f : α → β) (i : α) (hi : i ∈ s) :
    ∃ j ∈ representatives s f, f j = f i := by
  let fiber := s.filter (fun j => f j = f i)
  have hn : fiber.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  let j := fiber.min' hn
  have hj := Finset.min'_mem fiber hn
  refine ⟨j, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, ?_⟩, (Finset.mem_filter.mp hj).2⟩
  intro k hk he
  apply Finset.min'_le fiber k
  exact Finset.mem_filter.mpr ⟨hk, he.trans (Finset.mem_filter.mp hj).2⟩

theorem injective (s : Finset α) (f : α → β) : Set.InjOn f (representatives s f) := by
  intro i hi j hj he
  have hi' := Finset.mem_filter.mp hi
  have hj' := Finset.mem_filter.mp hj
  exact le_antisymm (hi'.2 j hj'.1 he.symm) (hj'.2 i hi'.1 he)

theorem image_eq (s : Finset α) (f : α → β) : (representatives s f).image f = s.image f := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩
  · intro hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, hj, he⟩ := representative_exists s f i hi
    exact Finset.mem_image.mpr ⟨j, hj, he⟩

noncomputable def rank (s : Finset α) (f : α → β) (x : β) : ℕ :=
  ((representatives s f).filter (fun i => f i < x)).card

theorem rank_eq (s : Finset α) (f : α → β) (x : β) :
    rank s f x = ((s.image f).filter (fun y => y < x)).card := by
  apply Finset.card_bij (fun i _ => f i)
  · intro i hi
    have H := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp H.1).1, rfl⟩, H.2⟩
  · intro i hi j hj he
    exact injective s f (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 he
  · intro y hy
    have H := Finset.mem_filter.mp hy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp H.1
    obtain ⟨j, hj, he⟩ := representative_exists s f i hi
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, he ▸ H.2⟩, he⟩

theorem rank_le (s : Finset α) (f : α → β) (x : β) : rank s f x ≤ s.card :=
  (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)

theorem rank_lt_rank (s : Finset α) (f : α → β) (i j : α) (hi : i ∈ s) (hlt : f i < f j) :
    rank s f (f i) < rank s f (f j) := by
  rw [rank_eq, rank_eq]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨fun y hy => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.trans hlt⟩, ?_⟩
  intro he
  have H : f i ∈ (s.image f).filter (fun y => y < f j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, hlt⟩
  rw [← he] at H
  exact lt_irrefl (f i) (Finset.mem_filter.mp H).2

theorem rank_eq_iff (s : Finset α) (f : α → β) (i j : α) (hi : i ∈ s) (hj : j ∈ s) :
    rank s f (f i) = rank s f (f j) ↔ f i = f j := by
  constructor
  · intro he
    rcases lt_trichotomy (f i) (f j) with hlt | heq | hgt
    · exact ((ne_of_lt (rank_lt_rank s f i j hi hlt)) he).elim
    · exact heq
    · exact ((ne_of_lt (rank_lt_rank s f j i hj hgt)) he.symm).elim
  · intro he
    rw [he]

theorem rank_eq_of_comparisons (s : Finset α) (f g : α → β) (i : α)
    (he : ∀ j ∈ s, ∀ k ∈ s, f j = f k ↔ g j = g k)
    (hl : ∀ j ∈ s, f j < f i ↔ g j < g i) : rank s f (f i) = rank s g (g i) := by
  apply congrArg Finset.card
  ext j
  simp only [representatives, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hj, hmin⟩, hjlt⟩
    exact ⟨⟨hj, fun k hk hkg => hmin k hk ((he k hk j hj).mpr hkg)⟩, (hl j hj).mp hjlt⟩
  · rintro ⟨⟨hj, hmin⟩, hjlt⟩
    exact ⟨⟨hj, fun k hk hkf => hmin k hk ((he k hk j hj).mp hkf)⟩, (hl j hj).mpr hjlt⟩

end LeanCanny.Geometry.FiniteImageRank

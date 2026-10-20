/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Interval.Finset.Fin

/-! # Decreasing coordinate positions and binomial mask counts

Subsets of a finite ordered coordinate set correspond to subsets of its
decreasing position list. A mask of cardinality `k+1` has a unique greatest
position. The masks whose greatest position is `j` are counted by
`Nat.choose j k`.
-/

@[expose] public section

namespace LeanCanny.Algebra.FinitePositionMasks
open Function
open scoped Classical
variable {α : Type*} [LinearOrder α]

abbrev CoordinateMask (A : Finset α) (k : ℕ) := {s : Finset α // s ⊆ A ∧ s.card = k}
abbrev PositionMask (q k : ℕ) := {s : Finset (Fin q) // s.card = k}

noncomputable def reverseRank (A : Finset α) : A ≃ Fin A.card :=
  (A.orderIsoOfFin rfl).symm.toEquiv.trans Fin.revPerm

theorem reverseRank_lt_iff (A : Finset α) (x y : A) : reverseRank A x < reverseRank A y ↔ y.val < x.val := by
  change Fin.rev ((A.orderIsoOfFin rfl).symm x) < Fin.rev ((A.orderIsoOfFin rfl).symm y) ↔ _
  rw [Fin.rev_lt_rev]
  exact (A.orderIsoOfFin rfl).symm.lt_iff_lt

theorem reverseRank_le_iff (A : Finset α) (x y : A) : reverseRank A x ≤ reverseRank A y ↔ y.val ≤ x.val := by
  change Fin.rev ((A.orderIsoOfFin rfl).symm x) ≤ Fin.rev ((A.orderIsoOfFin rfl).symm y) ↔ _
  rw [Fin.rev_le_rev]
  exact (A.orderIsoOfFin rfl).symm.le_iff_le

theorem reverseRank_val (A : Finset α) (x : A) :
    (reverseRank A x).val = (A.filter (fun y => x.val < y)).card := by
  let e : (A.filter (fun y => x.val < y)) ≃ {y : A // x.val < y.val} :=
    { toFun := fun y => ⟨⟨y.val, (Finset.mem_filter.mp y.property).1⟩, (Finset.mem_filter.mp y.property).2⟩
      invFun := fun y => ⟨y.val.val, Finset.mem_filter.mpr ⟨y.val.property, y.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let f : {y : A // x.val < y.val} ≃ (Finset.Iio (reverseRank A x)) :=
    (reverseRank A).subtypeEquiv (fun y => by
      simpa only [Finset.mem_Iio] using (reverseRank_lt_iff A y x).symm)
  have he := Fintype.card_congr (e.trans f)
  rw [Fintype.card_coe, Fintype.card_coe, Fin.card_Iio] at he
  exact he.symm

theorem subtype_map_inverse (A : Finset α) (u : Finset A) :
    (u.map (Embedding.subtype (· ∈ A))).subtype (· ∈ A) = u := by
  ext x
  rw [Finset.mem_subtype, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := Subtype.ext he
    simpa only [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

noncomputable def coordinateMaskEquiv (A : Finset α) (k : ℕ) :
    CoordinateMask A k ≃ PositionMask A.card k where
  toFun s := ⟨(reverseRank A).finsetCongr (s.val.subtype (· ∈ A)), by
    rw [Equiv.finsetCongr_apply, Finset.card_map]
    have he := congrArg Finset.card (Finset.subtype_map_of_mem (fun _ hx => s.property.1 hx))
    rw [Finset.card_map] at he
    exact he.trans s.property.2⟩
  invFun s := ⟨((reverseRank A).finsetCongr.symm s.val).map (Embedding.subtype (· ∈ A)),
    ⟨fun _ hx => Finset.property_of_mem_map_subtype _ hx, by
      change (((s.val.map (reverseRank A).symm.toEmbedding).map (Embedding.subtype (· ∈ A))).card) = k
      rw [Finset.card_map, Finset.card_map]
      exact s.property⟩⟩
  left_inv s := by
    apply Subtype.ext
    change (((reverseRank A).finsetCongr.symm ((reverseRank A).finsetCongr
      (s.val.subtype (· ∈ A)))).map (Embedding.subtype (· ∈ A))) = s.val
    rw [Equiv.symm_apply_apply]
    exact Finset.subtype_map_of_mem (fun _ hx => s.property.1 hx)
  right_inv s := by
    apply Subtype.ext
    change (reverseRank A).finsetCongr
      ((((reverseRank A).finsetCongr.symm s.val).map (Embedding.subtype (· ∈ A))).subtype (· ∈ A)) = s.val
    rw [subtype_map_inverse, Equiv.apply_symm_apply]

theorem card_positionMask (q k : ℕ) : Fintype.card (PositionMask q k) = q.choose k := by
  let e : PositionMask q k ≃ ((Finset.univ : Finset (Fin q)).powersetCard k) :=
    { toFun := fun s => ⟨s.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.property⟩⟩
      invFun := fun s => ⟨s.val, (Finset.mem_powersetCard.mp s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

theorem card_coordinateMask [Fintype α] (A : Finset α) (k : ℕ) :
    Fintype.card (CoordinateMask A k) = A.card.choose k := by
  rw [Fintype.card_congr (coordinateMaskEquiv A k), card_positionMask]

noncomputable def lastMasks (q k : ℕ) (j : Fin q) : Finset (Finset (Fin q)) :=
  ((Finset.Iic j).powersetCard (k + 1)).filter (fun s => j ∈ s)

theorem mem_lastMasks (q k : ℕ) (j : Fin q) (s : Finset (Fin q)) :
    s ∈ lastMasks q k j ↔ s ⊆ Finset.Iic j ∧ s.card = k + 1 ∧ j ∈ s := by
  simp only [lastMasks, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

theorem card_lastMasks (q k : ℕ) (j : Fin q) : (lastMasks q k j).card = j.val.choose k := by
  have he := Finset.card_filter_powersetCard_subset ({j} : Finset (Fin q)) (Finset.Iic j) (k + 1)
    (by simp only [Finset.singleton_subset_iff, Finset.mem_Iic, le_refl])
    (by simp only [Finset.card_singleton]; omega)
  simpa only [lastMasks, Finset.singleton_subset_iff, Fin.card_Iic, Finset.card_singleton, Nat.add_sub_cancel] using he

theorem coordinateMask_mem_last (A : Finset α) (k : ℕ) (s : CoordinateMask A (k + 1))
    (c : α) (hc : c ∈ s.val) (hmin : ∀ x ∈ s.val, c ≤ x) :
    (coordinateMaskEquiv A (k + 1) s).val ∈ lastMasks A.card k (reverseRank A ⟨c, s.property.1 hc⟩) := by
  rw [mem_lastMasks]
  refine ⟨?_, (coordinateMaskEquiv A (k + 1) s).property, ?_⟩
  · intro j hj
    change j ∈ (s.val.subtype (· ∈ A)).map (reverseRank A).toEmbedding at hj
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hj
    apply Finset.mem_Iic.mpr
    exact (reverseRank_le_iff A x ⟨c, s.property.1 hc⟩).mpr (hmin x.val (Finset.mem_subtype.mp hx))
  · change reverseRank A ⟨c, s.property.1 hc⟩ ∈ (s.val.subtype (· ∈ A)).map (reverseRank A).toEmbedding
    exact Finset.mem_map.mpr ⟨⟨c, s.property.1 hc⟩, Finset.mem_subtype.mpr hc, rfl⟩

noncomputable def lastMaskEquiv (q k : ℕ) (j : Fin q) :
    {s : PositionMask q (k + 1) // s.val ∈ lastMasks q k j} ≃ (lastMasks q k j) where
  toFun s := ⟨s.val.val, s.property⟩
  invFun s := ⟨⟨s.val, ((mem_lastMasks q k j s.val).mp s.property).2.1⟩, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_unique_last (q k : ℕ) (s : PositionMask q (k + 1)) : ∃! j : Fin q, s.val ∈ lastMasks q k j := by
  have hs : s.val.Nonempty := Finset.card_pos.mp (by rw [s.property]; omega)
  refine ⟨s.val.max' hs, ?_, ?_⟩
  · dsimp only
    rw [mem_lastMasks]
    refine ⟨?_, s.property, Finset.max'_mem _ _⟩
    intro i hi
    exact Finset.mem_Iic.mpr (Finset.le_max' _ _ hi)
  · intro j hj
    have he := (mem_lastMasks q k j s.val).mp hj
    apply le_antisymm
    · exact Finset.le_max' _ _ he.2.2
    · exact Finset.mem_Iic.mp (he.1 (Finset.max'_mem _ _))

end LeanCanny.Algebra.FinitePositionMasks

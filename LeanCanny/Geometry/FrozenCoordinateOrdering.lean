/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Logic.Equiv.Fin.Basic
/-! # An explicit frozen-first permutation for any proper coordinate subset -/
@[expose] public section
namespace LeanCanny.Geometry.FrozenCoordinateOrdering
open scoped Classical
variable {N : ℕ}

noncomputable def split (s : Finset (Fin N)) : Fin N ≃ Fin s.card ⊕ Fin (N-s.card) :=
  (finSumEquivOfFinset (s := s) (m := s.card) (n := N-s.card) rfl
    (by rw [Finset.card_compl, Fintype.card_fin])).symm

noncomputable def flatten (s : Finset (Fin N)) : Fin s.card ⊕ Fin (N-s.card) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le (by simpa using s.card_le_univ)))

noncomputable def permutation (s : Finset (Fin N)) : Equiv.Perm (Fin N) :=
  (flatten s).symm.trans (split s).symm

theorem permutation_flatten (s : Finset (Fin N)) (j : Fin s.card ⊕ Fin (N-s.card)) :
    permutation s (flatten s j) = (split s).symm j := by
  simp only [permutation, Equiv.trans_apply, Equiv.symm_apply_apply]

theorem first_mem (s : Finset (Fin N)) (j : Fin s.card) : (split s).symm (.inl j) ∈ s := by
  exact s.orderEmbOfFin_mem rfl j

theorem last_notMem (s : Finset (Fin N)) (j : Fin (N-s.card)) : (split s).symm (.inr j) ∉ s := by
  exact Finset.mem_compl.mp (sᶜ.orderEmbOfFin_mem (by rw [Finset.card_compl, Fintype.card_fin]) j)

theorem permutation_mem_iff (s : Finset (Fin N)) (j : Fin N) : permutation s j ∈ s ↔ j.val < s.card := by
  obtain ⟨j,rfl⟩ := (flatten s).surjective j
  rw [permutation_flatten]
  cases j with
  | inl j => exact iff_of_true (first_mem s j) j.isLt
  | inr j =>
    apply iff_of_false (last_notMem s j)
    change ¬ s.card + j.val < s.card
    omega

theorem inverse_mem_iff (s : Finset (Fin N)) (j : Fin N) : ((permutation s).symm j).val < s.card ↔ j ∈ s := by
  simpa only [Equiv.apply_symm_apply] using (permutation_mem_iff s ((permutation s).symm j)).symm

theorem card_lt (s : Finset (Fin N)) (j : Fin N) (hj : j ∉ s) : s.card < N := by
  have H := (permutation s).symm j |>.isLt
  have HJ : ¬ ((permutation s).symm j).val < s.card := fun h => hj ((inverse_mem_iff s j).mp h)
  omega

end LeanCanny.Geometry.FrozenCoordinateOrdering

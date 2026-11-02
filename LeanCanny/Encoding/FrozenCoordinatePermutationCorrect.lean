/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FrozenCoordinatePermutationFP
public import LeanCanny.Geometry.FrozenCoordinateOrdering
/-! # The mask partition reader is the exact frozen-first coordinate permutation -/
@[expose] public section
namespace LeanCanny.Encoding.FrozenCoordinatePermutationBits
open LeanCanny.Geometry
open scoped Classical
variable {N : ℕ}

def mask (s : Finset (Fin N)) := List.ofFn (fun i : Fin N => decide (i ∈ s))

theorem mask_get (s : Finset (Fin N)) (i : Fin N) : (mask s)[i.val]?.getD false = decide (i ∈ s) := by
  unfold mask
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt), Option.getD_some, List.getElem_ofFn]

theorem finRange_values (N : ℕ) : (List.finRange N).map Fin.val = List.range N := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    rfl

theorem sort_filter (s : Finset (Fin N)) :
    s.sort = (List.finRange N).filter (fun i => decide (i ∈ s)) := by
  apply s.sortedLT_sort.eq_of_mem_iff (List.Pairwise.filter _ (List.sortedLT_finRange N).pairwise).sortedLT
  intro i
  simp

theorem selected_mask (s : Finset (Fin N)) (b : Bool) :
    selected (mask s) b = (if b then s.sort else sᶜ.sort).map Fin.val := by
  unfold selected
  rw [show (mask s).length = N by simp only [mask, List.length_ofFn], ← finRange_values N, List.filter_map]
  cases b with
  | true =>
    simp only [ite_true]
    rw [sort_filter s]
    apply congrArg (List.map Fin.val)
    apply List.filter_congr
    intro i _
    simp only [Function.comp_apply, mask_get]
    by_cases hm : i ∈ s <;> simp [hm]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [sort_filter sᶜ]
    apply congrArg (List.map Fin.val)
    apply List.filter_congr
    intro i _
    simp only [Function.comp_apply, mask_get, Finset.mem_compl]
    by_cases hm : i ∈ s <;> simp [hm]

theorem permutation_get (s : Finset (Fin N)) (j : Fin N) :
    FrozenCoordinateOrdering.permutation s j = (s.sort ++ sᶜ.sort)[j.val]'(by
      simp only [List.length_append, Finset.length_sort, Finset.card_compl, Fintype.card_fin]
      have H : s.card ≤ N := by simpa only [Finset.card_univ, Fintype.card_fin] using s.card_le_univ
      omega) := by
  obtain ⟨i, rfl⟩ := (FrozenCoordinateOrdering.flatten s).surjective j
  rw [FrozenCoordinateOrdering.permutation_flatten]
  cases i with
  | inl i =>
    change s.orderEmbOfFin rfl i = (s.sort ++ sᶜ.sort)[i.val]'(by simp only [List.length_append, Finset.length_sort]; have H := i.isLt; omega)
    rw [List.getElem_append_left (by simpa only [Finset.length_sort] using i.isLt), Finset.orderEmbOfFin_apply]
    simp only [Fin.getElem_fin]
  | inr i =>
    change sᶜ.orderEmbOfFin (by rw [Finset.card_compl, Fintype.card_fin]) i = (s.sort ++ sᶜ.sort)[s.card + i.val]'(by
      simp only [List.length_append, Finset.length_sort, Finset.card_compl, Fintype.card_fin]; have H := i.isLt; omega)
    rw [List.getElem_append_right (by rw [Finset.length_sort]; omega)]
    simp only [Finset.length_sort, Nat.add_sub_cancel_left, Finset.orderEmbOfFin_apply, Fin.getElem_fin]

theorem reader_mask (s : Finset (Fin N)) (j : Fin N) :
    reader (pair (mask s) (BinaryNatCode.encode j.val)) =
      BinaryNatCode.encode (FrozenCoordinateOrdering.permutation s j).val := by
  rw [reader_packet]
  have HP : partition (mask s) = (s.sort ++ sᶜ.sort).map Fin.val := by
    simp only [partition, selected_mask, ite_true, Bool.false_eq_true, ite_false, List.map_append]
  rw [HP]
  have HN : ((s.sort ++ sᶜ.sort).map Fin.val).length = N := by
    simp only [List.length_map, List.length_append, Finset.length_sort, Finset.card_compl, Fintype.card_fin]
    have H : s.card ≤ N := by simpa only [Finset.card_univ, Fintype.card_fin] using s.card_le_univ
    omega
  rw [List.getElem?_eq_getElem (HN.symm ▸ j.isLt), Option.getD_some, List.getElem_map, ← permutation_get s j]
end LeanCanny.Encoding.FrozenCoordinatePermutationBits

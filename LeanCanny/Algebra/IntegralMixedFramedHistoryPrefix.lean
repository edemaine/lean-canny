/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryOrigin
/-! # Chronological total prefixes retain each source-framed instruction -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical

def chronological {n B : ℕ} (cs : List (Instruction n B)) (birth : ℕ) : Option (Instruction n B) := cs.reverse[birth]?

theorem chronological_older {n B : ℕ} (cs : List (Instruction n B)) (i : Fin cs.length) :
    chronological cs (older cs i).length=some (chosen cs i) := by
  unfold chronological
  rw [older_length]
  rw [List.getElem?_reverse' (l := cs) (i := cs.length-1-i.val) (j := i.val) (by have H := i.isLt; omega)]
  exact List.getElem?_eq_getElem i.isLt

def past {n B : ℕ} (cs : List (Instruction n B)) (birth : ℕ) := (cs.reverse.take birth).reverse

noncomputable def paddedPast {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ) :=
  List.replicate (birth - cs.length) default ++ past cs birth

theorem past_length {n B : ℕ} (cs : List (Instruction n B)) (birth : ℕ) :
    (past cs birth).length = min birth cs.length := by simp only [past, List.length_reverse, List.length_take]

theorem paddedPast_length {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ) :
    (paddedPast default cs birth).length = birth := by
  simp only [paddedPast, List.length_append, List.length_replicate, past_length]
  omega

theorem paddedPast_valid {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ) (hb : birth ≤ cs.length) :
    paddedPast default cs birth = past cs birth := by
  simp only [paddedPast, Nat.sub_eq_zero_of_le hb, List.replicate_zero, List.nil_append]

theorem paddedPast_full {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) : paddedPast default cs cs.length = cs := by
  rw [paddedPast_valid default cs _ le_rfl]
  unfold past
  rw [show cs.reverse.take cs.length = cs.reverse from List.take_of_length_le (by rw [List.length_reverse]), List.reverse_reverse]

theorem past_chronological {n B : ℕ} (cs : List (Instruction n B)) (birth i : ℕ) (hi : i < birth) :
    chronological (past cs birth) i = chronological cs i := by
  unfold chronological past
  rw [List.reverse_reverse, List.getElem?_take]
  simp only [hi, ite_true]

theorem paddedPast_chronological_valid {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth i : ℕ)
    (hb : birth ≤ cs.length) (hi : i < birth) : chronological (paddedPast default cs birth) i = chronological cs i := by
  rw [paddedPast_valid default cs birth hb]
  exact past_chronological cs birth i hi

theorem paddedPast_eq_take_pad {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth pad : ℕ) (hb : birth ≤ pad) :
    paddedPast default cs birth = ((cs.reverse ++ List.replicate pad default).take birth).reverse := by
  rw [List.take_append, List.length_reverse, List.take_replicate, min_eq_left ((Nat.sub_le _ _).trans hb), List.reverse_append, List.reverse_replicate]
  rfl

theorem paddedPast_drop {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth olderBirth : ℕ) (hb : olderBirth ≤ birth) :
    (paddedPast default cs birth).drop (birth - olderBirth) = paddedPast default cs olderBirth := by
  rw [paddedPast_eq_take_pad default cs birth birth le_rfl, paddedPast_eq_take_pad default cs olderBirth birth hb, List.drop_reverse]
  have HL : (List.take birth (cs.reverse ++ List.replicate birth default)).length = birth := by
    rw [List.length_take, List.length_append, List.length_reverse, List.length_replicate, min_eq_left (by omega)]
  rw [HL, Nat.sub_sub_self hb, List.take_take, min_eq_left hb]

theorem paddedPast_older {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ)
    (i : Fin (paddedPast default cs birth).length) : older (paddedPast default cs birth) i = paddedPast default cs (birth - 1 - i.val) := by
  unfold older
  have HI : i.val < birth := lt_of_lt_of_eq i.isLt (paddedPast_length default cs birth)
  have HE : i.val + 1 = birth - (birth - 1 - i.val) := by omega
  rw [HE]
  exact paddedPast_drop default cs birth _ (by omega)

theorem paddedPast_chronological {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth i : ℕ) (hi : i < birth) :
    chronological (paddedPast default cs birth) i = some ((chronological cs i).getD default) := by
  rw [paddedPast_eq_take_pad default cs birth birth le_rfl]
  unfold chronological
  rw [List.reverse_reverse, List.getElem?_take]
  simp only [hi, ite_true]
  by_cases hc : i < cs.length
  · rw [List.getElem?_append_left (by simpa only [List.length_reverse] using hc),
      List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hc)]
    rfl
  · rw [List.getElem?_append_right (by simp only [List.length_reverse]; omega), List.length_reverse,
      List.getElem?_replicate_of_lt ((Nat.sub_le _ _).trans_lt hi), List.getElem?_eq_none (by simp only [List.length_reverse]; omega)]
    rfl
end LeanCanny.Algebra.IntegralMixedFramedHistoryScript

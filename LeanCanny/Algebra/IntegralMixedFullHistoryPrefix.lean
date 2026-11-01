/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHistoryOrigin
/-! # Literal total scalar prefixes of full mixed histories

A valid chronological prefix keeps the actual commands. Beyond the script
end, integer X births pad the prefix to the requested scalar arity. Thus
total word decoders may preserve their birth field without inventing a
physical command cursor or postulating a state-computability oracle.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHistoryScript
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def defaultCommand {n B : ℕ} {P : SpatialSource n} : Command P B :=
  .integer Polynomial.X Polynomial.X_ne_zero (by simpa only [Polynomial.natDegree_X] using (Nat.one_le_two_pow : 1 ≤ 2 ^ B))

def past {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) := (cs.reverse.take birth).reverse

noncomputable def paddedPast {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) :=
  List.replicate (birth - cs.length) defaultCommand ++ past cs birth

theorem past_length {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) :
    (past cs birth).length = min birth cs.length := by simp only [past, List.length_reverse, List.length_take]

theorem paddedPast_length {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) :
    (paddedPast cs birth).length = birth := by
  simp only [paddedPast, List.length_append, List.length_replicate, past_length]
  omega

theorem paddedPast_valid {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) (hb : birth ≤ cs.length) :
    paddedPast cs birth = past cs birth := by
  simp only [paddedPast, Nat.sub_eq_zero_of_le hb, List.replicate_zero, List.nil_append]

theorem paddedPast_full {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) : paddedPast cs cs.length = cs := by
  rw [paddedPast_valid cs _ le_rfl]
  unfold past
  rw [show cs.reverse.take cs.length = cs.reverse from List.take_of_length_le (by rw [List.length_reverse]), List.reverse_reverse]

theorem past_chronological {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth i : ℕ) (hi : i < birth) :
    chronological (past cs birth) i = chronological cs i := by
  unfold chronological past
  rw [List.reverse_reverse, List.getElem?_take]
  simp only [hi, ite_true]

theorem paddedPast_chronological_valid {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth i : ℕ)
    (hb : birth ≤ cs.length) (hi : i < birth) : chronological (paddedPast cs birth) i = chronological cs i := by
  rw [paddedPast_valid cs birth hb]
  exact past_chronological cs birth i hi

noncomputable def stateAt {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Command P B)) (birth : ℕ) (hb : birth ≤ S + 1) :=
  run initial (paddedPast cs birth) (by rw [paddedPast_length]; exact hb)

theorem stateAt_scalar_arity {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ) :
    (paddedPast cs birth).length = birth := paddedPast_length cs birth

theorem stateAt_bank_length {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs : List (Command P B)) (birth : ℕ) (hb : birth ≤ S + 1) :
    (List.ofFn (stateAt initial cs birth hb).bank.denominator).length = birth := by
  rw [List.length_ofFn, paddedPast_length]

theorem stateAt_canonical {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (H : Canonical initial) (cs : List (Command P B)) (birth : ℕ) (hb : birth ≤ S + 1) :
    Canonical (stateAt initial cs birth hb) := run_canonical initial H _ _

theorem paddedPast_eq_take_pad {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth pad : ℕ) (hb : birth ≤ pad) :
    paddedPast cs birth = ((cs.reverse ++ List.replicate pad defaultCommand).take birth).reverse := by
  rw [List.take_append, List.length_reverse, List.take_replicate, min_eq_left ((Nat.sub_le _ _).trans hb), List.reverse_append, List.reverse_replicate]
  rfl

theorem paddedPast_drop {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth olderBirth : ℕ) (hb : olderBirth ≤ birth) :
    (paddedPast cs birth).drop (birth - olderBirth) = paddedPast cs olderBirth := by
  rw [paddedPast_eq_take_pad cs birth birth le_rfl, paddedPast_eq_take_pad cs olderBirth birth hb, List.drop_reverse]
  have HL : (List.take birth (cs.reverse ++ List.replicate birth defaultCommand)).length = birth := by
    rw [List.length_take, List.length_append, List.length_reverse, List.length_replicate, min_eq_left (by omega)]
  rw [HL, Nat.sub_sub_self hb, List.take_take, min_eq_left hb]

theorem paddedPast_older {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth : ℕ)
    (i : Fin (paddedPast cs birth).length) : older (paddedPast cs birth) i = paddedPast cs (birth - 1 - i.val) := by
  unfold older
  have HI : i.val < birth := lt_of_lt_of_eq i.isLt (paddedPast_length cs birth)
  have HE : i.val + 1 = birth - (birth - 1 - i.val) := by omega
  rw [HE]
  exact paddedPast_drop cs birth _ (by omega)

theorem paddedPast_chronological {n B : ℕ} {P : SpatialSource n} (cs : List (Command P B)) (birth i : ℕ) (hi : i < birth) :
    chronological (paddedPast cs birth) i = some ((chronological cs i).getD defaultCommand) := by
  rw [paddedPast_eq_take_pad cs birth birth le_rfl]
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
end LeanCanny.Algebra.IntegralMixedFullHistoryScript

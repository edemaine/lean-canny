/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryPrefix
/-! # The next actual framed instruction extends the literal padded past

This identity includes beyond-end default instructions. No existing command
is changed to query a lower cut choice, and no old source is reinterpreted.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryScript
open IntegralMixedHistory

theorem paddedPast_succ {n B : ℕ} (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ) :
    paddedPast default cs (birth+1)=(chronological cs birth).getD default::paddedPast default cs birth := by
  by_cases hb : birth<cs.length
  · have hr : birth<cs.reverse.length := by simpa only [List.length_reverse] using hb
    rw [paddedPast_valid default cs (birth+1) (by omega),paddedPast_valid default cs birth hb.le]
    unfold past chronological
    rw [List.take_succ_eq_append_getElem hr,List.reverse_append,List.reverse_singleton,List.getElem?_eq_getElem hr]
    rfl
  · have ho : past cs birth=cs := by
      unfold past
      rw [List.take_of_length_le (by simp only [List.length_reverse]; omega),List.reverse_reverse]
    have hn : past cs (birth+1)=cs := by
      unfold past
      rw [List.take_of_length_le (by simp only [List.length_reverse]; omega),List.reverse_reverse]
    have hc : chronological cs birth=none := List.getElem?_eq_none (by simp only [List.length_reverse]; omega)
    unfold paddedPast
    rw [ho,hn,hc]
    simp only [Option.getD_none]
    have he : birth+1-cs.length=(birth-cs.length)+1 := by omega
    rw [he,List.replicate_succ]
    rfl

private theorem run_prefix_congr {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B 0 ι) (cs ds : List (Instruction n B)) (he : cs=ds)
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) :
    HEq (run x cs hc).sampler.scalarPrefix (run x ds hd).sampler.scalarPrefix := by cases he; rfl

theorem padded_run_successor {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B 0 ι) (default : Instruction n B) (cs : List (Instruction n B)) (birth : ℕ)
    (hb : birth≤S)
    (hnew : (paddedPast default cs (birth+1)).length≤S+1) :
    HEq (run x (paddedPast default cs (birth+1)) hnew).sampler.scalarPrefix
      (run x ((chronological cs birth).getD default::paddedPast default cs birth)
        (by rw [List.length_cons,paddedPast_length]; omega)).sampler.scalarPrefix :=
  run_prefix_congr x _ _ (paddedPast_succ default cs birth) hnew _

end LeanCanny.Algebra.IntegralMixedFramedHistoryScript

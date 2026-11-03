/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlanSuccessor
/-! # A causal command prefix depends only on its original record prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPrefixCongruence
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedCausalPlanBits (commands commands_cons commands_length)
open scoped Classical

variable {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

noncomputable def prefixRun (x : State P S B 0 ι) (rs : List (Record n B)) (hr : rs.length≤S+1)
    (fallback : Instruction n B) (j : ℕ) (hj : j≤rs.length) :=
  run x (paddedPast fallback (commands x rs hr) j) (by rw [paddedPast_length];exact hj.trans hr)

theorem commands_drop (x : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) (k : ℕ) :
    (commands x rs h).drop k=commands x (rs.drop k) (by
      simp only [List.length_drop];exact (Nat.sub_le _ _).trans h) :=by
  induction k generalizing rs with
  | zero=>rfl
  | succ k ih=>
    cases rs with
    | nil=>rfl
    | cons r rs=>
      rw [commands_cons]
      simp only [List.drop_succ_cons]
      exact ih rs _

theorem commands_prefix (x : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1)
    (fallback : Instruction n B) (j : ℕ) (hj : j≤rs.length) :
    paddedPast fallback (commands x rs h) j=
      commands x ((rs.reverse.take j).reverse) (by
        simp only [List.length_reverse,List.length_take]
        exact (min_le_right _ _).trans h) :=by
  rw [paddedPast_valid _ _ _ (by rw [commands_length];exact hj)]
  simp only [past,List.reverse_take,List.length_reverse,List.reverse_reverse]
  rw [commands_length,commands_drop]

private theorem commands_congr (x : State P S B 0 ι) (rs ds : List (Record n B))
    (h : rs=ds) (hr : rs.length≤S+1) (hd : ds.length≤S+1) :commands x rs hr=commands x ds hd :=by
  cases h
  rfl

theorem prefix_eq (x : State P S B 0 ι) (rs ds : List (Record n B))
    (hr : rs.length≤S+1) (hd : ds.length≤S+1) (fr fd : Instruction n B)
    (j : ℕ) (hjr : j≤rs.length) (hjd : j≤ds.length) (hp : rs.reverse.take j=ds.reverse.take j) :
    paddedPast fr (commands x rs hr) j=paddedPast fd (commands x ds hd) j :=by
  rw [commands_prefix x rs hr fr j hjr,commands_prefix x ds hd fd j hjd]
  exact commands_congr x _ _ (congrArg List.reverse hp) _ _

private theorem run_congr (x : State P S B 0 ι) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (h : cs=ds) :HEq (run x cs hc) (run x ds hd) :=by
  cases h
  rfl

theorem run_prefix (x : State P S B 0 ι) (rs ds : List (Record n B))
    (hr : rs.length≤S+1) (hd : ds.length≤S+1) (fr fd : Instruction n B)
    (j : ℕ) (hjr : j≤rs.length) (hjd : j≤ds.length) (hp : rs.reverse.take j=ds.reverse.take j) :
    HEq (run x (paddedPast fr (commands x rs hr) j) (by rw [paddedPast_length];exact hjr.trans hr))
      (run x (paddedPast fd (commands x ds hd) j) (by rw [paddedPast_length];exact hjd.trans hd)) :=
  run_congr x _ _ _ _ (prefix_eq x rs ds hr hd fr fd j hjr hjd hp)
end LeanCanny.Algebra.IntegralMixedCausalPrefixCongruence

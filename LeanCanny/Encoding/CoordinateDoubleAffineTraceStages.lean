/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTrace

/-! # Uniform stage selection from a coordinate-child history -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

theorem offset_concat (a b : List Bool) : offset (a ++ b) = offset a + offset b := by
  simp only [offset, List.length_append, List.count_append]
  omega

theorem offset_take_le (trace : List Bool) (i : ℕ) : offset (trace.take i) ≤ offset trace := by
  have H := offset_concat (trace.take i) (trace.drop i)
  rw [List.take_append_drop] at H
  omega

def completed (initialDepth : ℕ) (trace : List Bool) (k : ℕ) : ℕ :=
  ((Finset.range trace.length).filter (fun i => initialDepth + offset (trace.take (i + 1)) ≤ k)).card

theorem completed_le (d : ℕ) (trace : List Bool) (k : ℕ) : completed d trace k ≤ trace.length := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem completed_of_depth_le (d : ℕ) (trace : List Bool) (k : ℕ) (hk : d + offset trace ≤ k) :
    completed d trace k = trace.length := by
  unfold completed
  rw [Finset.filter_eq_self.mpr (fun i _ => (Nat.add_le_add_left (offset_take_le trace (i + 1)) d).trans hk)]
  exact Finset.card_range _

theorem completed_append (d : ℕ) (trace : List Bool) (midpoint : Bool) (k : ℕ) :
    completed d (trace ++ [midpoint]) k = completed d trace k +
      if d + offset (trace ++ [midpoint]) ≤ k then 1 else 0 := by
  have H : ((Finset.range trace.length).filter
      (fun i => d + offset ((trace ++ [midpoint]).take (i + 1)) ≤ k)) =
    ((Finset.range trace.length).filter (fun i => d + offset (trace.take (i + 1)) ≤ k)) := by
    apply Finset.filter_congr
    intro i hi
    rw [List.take_append_of_le_length (by have := Finset.mem_range.mp hi; omega)]
  have hn : trace.length ∉ ((Finset.range trace.length).filter
      (fun i => d + offset (trace.take (i + 1)) ≤ k)) := by
    intro h
    have := Finset.mem_range.mp (Finset.mem_filter.mp h).1
    omega
  simp only [completed, List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  rw [H]
  have ht : (trace ++ [midpoint]).take (trace.length + 1) = trace ++ [midpoint] := by
    apply List.take_of_length_le
    simp only [List.length_append, List.length_singleton, le_refl]
  rw [ht]
  split_ifs
  · rw [Finset.card_insert_of_notMem hn]
  · omega

theorem completed_unary {d k : List Bool → ℕ} {trace : List Bool → List Bool}
    (hd : UnaryFn d) (ht : trace ∈ FP) (hk : BinaryFn k) :
    UnaryFn (fun q => completed (d q) (trace q) (k q)) := by
  have hp := (BinaryFn.ofUnary ((hd.comp pairFst_mem_FP).add
    (offset_unary (take_mem_FP (mem_FP_comp pairFst_mem_FP ht) (UnaryFn.index.add (UnaryFn.const 1)))))).le
      (hk.comp pairFst_mem_FP)
  apply ((UnaryFn.length ht).count hp).of_eq
  intro q
  simp only [completed, Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate]

def objectiveAt (initialDepth : ℕ) (seed : ℕ → ℕ) (trace : List Bool) (k : ℕ) : ℕ :=
  if k < initialDepth then seed k else seed initialDepth + completed initialDepth trace k

theorem objectiveAt_depth (d : ℕ) (seed : ℕ → ℕ) (trace : List Bool) :
    objectiveAt d seed trace (d + offset trace) = seed d + trace.length := by
  rw [objectiveAt, ite_eq_right (by omega), completed_of_depth_le d trace _ (le_refl _)]

theorem objectiveAt_append (d : ℕ) (seed : ℕ → ℕ) (trace : List Bool) (midpoint : Bool) (k : ℕ)
    (hk : k ≤ d + offset (trace ++ [midpoint])) :
    objectiveAt d seed (trace ++ [midpoint]) k =
      if k < d + offset trace then objectiveAt d seed trace k else
        objectiveAt d seed trace (d + offset trace) +
          if k = d + offset (trace ++ [midpoint]) then 1 else 0 := by
  have hc : 0 < CoordinateDoubleAffineChildRecords.copies midpoint := by cases midpoint <;> decide
  have ho := offset_append trace midpoint
  by_cases hb : k < d + offset trace
  · rw [ite_eq_left hb]
    unfold objectiveAt
    split_ifs with h
    · rfl
    · rw [completed_append, ite_eq_right (by omega), Nat.add_zero]
  · rw [ite_eq_right hb, objectiveAt_depth]
    rw [objectiveAt, ite_eq_right (by omega), completed_append,
      completed_of_depth_le d trace k (by omega)]
    by_cases he : k = d + offset (trace ++ [midpoint])
    · rw [ite_eq_left (by omega), ite_eq_left he]
      omega
    · rw [ite_eq_right (by omega), ite_eq_right he]
      omega

end LeanCanny.Encoding.CoordinateDoubleAffineTrace

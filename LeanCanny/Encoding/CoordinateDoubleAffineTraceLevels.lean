/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceObjectives
public import LeanCanny.Encoding.CoordinateDoubleAffineTraceLevelStability

/-! # Level records selected directly from a shared-source history -/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

def record (midpoint : Bool) (n coordinate ancestor : ℕ) : List Bool :=
  if midpoint then CoordinateHeightRecord.midpoint n coordinate ancestor (ancestor + 1)
  else CoordinateHeightRecord.height n coordinate ancestor

def generated (n d c : ℕ) (trace : List Bool) (i : ℕ) : List Bool :=
  record ((trace)[i]?.getD false) n (c + i) (d + offset (trace.take i))

theorem generated_FP {n d c i : List Bool → ℕ} {trace : List Bool → List Bool}
    (hn : UnaryFn n) (hd : UnaryFn d) (hc : UnaryFn c) (ht : trace ∈ FP) (hi : UnaryFn i) :
    (fun q => generated (n q) (d q) (c q) (trace q) (i q)) ∈ FP := by
  have ha := hd.add (offset_unary (take_mem_FP ht hi))
  exact (FPPred.getBit ht hi).ite_mem_FP
    (CoordinateHeightRecord.midpoint_FP hn (BinaryFn.ofUnary (hc.add hi))
      (BinaryFn.ofUnary ha) (BinaryFn.ofUnary (ha.add (UnaryFn.const 1))))
    (CoordinateHeightRecord.height_FP hn (BinaryFn.ofUnary (hc.add hi)) (BinaryFn.ofUnary ha))

theorem generated_append_old (n d c : ℕ) (trace : List Bool) (midpoint : Bool) (i : ℕ)
    (hi : i < trace.length) : generated n d c (trace ++ [midpoint]) i = generated n d c trace i := by
  rw [generated, generated, List.getElem?_append_left hi, List.take_append_of_le_length hi.le]

theorem generated_append_new (n d c : ℕ) (trace : List Bool) (midpoint : Bool) :
    generated n d c (trace ++ [midpoint]) trace.length = record midpoint n (c + trace.length) (d + offset trace) := by
  simp only [generated, List.getElem?_append, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some, List.take_append_of_le_length (le_refl trace.length), List.take_length]

theorem freeze_record (midpoint : Bool) (n c d m : ℕ)
    (hm : d + CoordinateDoubleAffineChildRecords.copies midpoint ≤ m) :
    FlatAffineFrozenLevelRecord.freeze m (record midpoint n c d) = record midpoint n c d := by
  cases midpoint
  · exact FlatAffineFrozenLevelRecord.freeze_height n c d m (by change d + 1 ≤ m at hm; omega)
  · exact FlatAffineFrozenLevelRecord.freeze_midpoint n c d (d + 1) m
      (by change d + 2 ≤ m at hm; omega) (by change d + 2 ≤ m at hm; omega)

theorem freeze_generated (n d c m : ℕ) (trace : List Bool) (i : ℕ) (hi : i < trace.length)
    (hm : d + offset (trace.take (i + 1)) ≤ m) :
    FlatAffineFrozenLevelRecord.freeze m (generated n d c trace i) = generated n d c trace i := by
  have H : offset (trace.take (i + 1)) = offset (trace.take i) +
      CoordinateDoubleAffineChildRecords.copies ((trace)[i]?.getD false) := by
    rw [List.take_succ_eq_append_getElem hi, offset_append, List.getElem?_eq_getElem hi, Option.getD_some]
  apply freeze_record
  rw [H] at hm
  omega

def levelAt (n d c : ℕ) (trace : List Bool) (seed : ℕ → ℕ → List Bool) (k j : ℕ) : List Bool :=
  if k < d then seed k j else
    if c ≤ j ∧ j < c + completed d trace k then generated n d c trace (min (j - c) trace.length) else
      if trace = [] then seed d j else FlatAffineFrozenLevelRecord.freeze d (seed d j)

end LeanCanny.Encoding.CoordinateDoubleAffineTrace

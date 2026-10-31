/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineChildBounds
public import LeanCanny.Encoding.BracketsFP

/-! # Shared-source traces for recursive coordinate children

One history bit selects a fixed-height or midpoint child. The original
source occurs once in the frame. Appending history adds one bit, and the
ancestry budget is bounded by the original coordinate rank.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTrace
open LeanCanny.Computation
set_option backward.isDefEq.respectTransparency false

abbrev base : List Bool → List Bool := LeanCanny.pairFst
abbrev history : List Bool → List Bool := LeanCanny.pairSnd

def frame (u trace : List Bool) : List Bool := LeanCanny.pair u trace

def append (midpoint : Bool) (q : List Bool) : List Bool := frame (base q) (history q ++ [midpoint])

theorem append_FP (midpoint : Bool) : append midpoint ∈ FP :=
  mem_FP_pair pairFst_mem_FP (appendFn_mem_FP pairSnd_mem_FP (constFn_mem_FP [midpoint]))

theorem base_frame (u trace : List Bool) : base (frame u trace) = u := LeanCanny.pairFst_pair u trace

theorem history_frame (u trace : List Bool) : history (frame u trace) = trace := LeanCanny.pairSnd_pair u trace

theorem append_frame (midpoint : Bool) (u trace : List Bool) :
    append midpoint (frame u trace) = frame u (trace ++ [midpoint]) := by
  simp only [append, base_frame, history_frame]

theorem base_append (midpoint : Bool) (q : List Bool) : base (append midpoint q) = base q := base_frame _ _

theorem history_append (midpoint : Bool) (q : List Bool) : history (append midpoint q) = history q ++ [midpoint] := history_frame _ _

theorem frame_length (u trace : List Bool) : (frame u trace).length = 2 * u.length + 2 + trace.length :=
  LeanCanny.pair_length u trace

theorem append_frame_length (midpoint : Bool) (u trace : List Bool) :
    (append midpoint (frame u trace)).length = (frame u trace).length + 1 := by
  simp only [append_frame, frame_length, List.length_append, List.length_singleton]
  omega

def offset (trace : List Bool) : ℕ := trace.length + trace.count true

theorem offset_append (trace : List Bool) (midpoint : Bool) :
    offset (trace ++ [midpoint]) = offset trace + CoordinateDoubleAffineChildRecords.copies midpoint := by
  cases midpoint <;> simp [offset, List.count_append, CoordinateDoubleAffineChildRecords.copies] <;> omega

theorem offset_le (trace : List Bool) : offset trace ≤ 2 * trace.length := by
  have H : trace.count true ≤ trace.length := List.count_le_length
  unfold offset
  omega

theorem length_le_offset (trace : List Bool) : trace.length ≤ offset trace := Nat.le_add_right _ _

theorem offset_unary {trace : List Bool → List Bool} (ht : trace ∈ FP) : UnaryFn (fun q => offset (trace q)) :=
  (UnaryFn.length ht).add (Brackets.countTrue_unary.comp ht)

def readers (P : BoundedFullWriter.Readers) : BoundedFullWriter.Readers := P.comp base

theorem readers_polyTime {P : BoundedFullWriter.Readers} (hP : P.PolyTime) : (readers P).PolyTime :=
  hP.comp pairFst_mem_FP

def depth (initial : List Bool → ℕ) (q : List Bool) : ℕ := initial (base q) + offset (history q)

def coordinate (initial : List Bool → ℕ) (q : List Bool) : ℕ := initial (base q) + (history q).length

def rank (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ) (q : List Bool) : ℕ :=
  P.dim (base q) + 3 - coordinate initial q

def Valid (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ) (q : List Bool) : Prop :=
  coordinate initial q ≤ P.dim (base q) + 3

theorem depth_unary {initial : List Bool → ℕ} (hi : UnaryFn initial) : UnaryFn (depth initial) :=
  (hi.comp pairFst_mem_FP).add (offset_unary pairSnd_mem_FP)

theorem coordinate_unary {initial : List Bool → ℕ} (hi : UnaryFn initial) : UnaryFn (coordinate initial) :=
  (hi.comp pairFst_mem_FP).add (UnaryFn.length pairSnd_mem_FP)

theorem rank_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {initial : List Bool → ℕ} (hi : UnaryFn initial) : UnaryFn (rank P initial) :=
  ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 3)).sub (coordinate_unary hi)

theorem valid_fppred {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {initial : List Bool → ℕ} (hi : UnaryFn initial) : FPPred (Valid P initial) :=
  FPPred.le (coordinate_unary hi) ((hP.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))

theorem depth_append (midpoint : Bool) (initial : List Bool → ℕ) (q : List Bool) :
    depth initial (append midpoint q) = depth initial q + CoordinateDoubleAffineChildRecords.copies midpoint := by
  simp only [depth, base_append, history_append, offset_append]
  omega

theorem coordinate_append (midpoint : Bool) (initial : List Bool → ℕ) (q : List Bool) :
    coordinate initial (append midpoint q) = coordinate initial q + 1 := by
  simp only [coordinate, base_append, history_append, List.length_append, List.length_singleton]
  omega

theorem valid_append (midpoint : Bool) (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ)
    (q : List Bool) (hn : coordinate initial q < P.dim (base q) + 3) : Valid P initial (append midpoint q) := by
  unfold Valid
  rw [coordinate_append, base_append]
  omega

theorem rank_decreases (midpoint : Bool) (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ)
    (q : List Bool) (hn : coordinate initial q < P.dim (base q) + 3) :
    rank P initial (append midpoint q) < rank P initial q := by
  simp only [rank, base_append, coordinate_append]
  omega

theorem ancestry_budget (P : BoundedFullWriter.Readers) (initialDepth initialCoordinate : List Bool → ℕ)
    (q : List Bool) (hv : Valid P initialCoordinate q) :
    depth initialDepth q + 2 * rank P initialCoordinate q ≤
      initialDepth (base q) + 2 * (P.dim (base q) + 3 - initialCoordinate (base q)) := by
  have H := offset_le (history q)
  unfold Valid coordinate at hv
  unfold depth rank coordinate
  omega

theorem history_bound (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ)
    (q : List Bool) (hv : Valid P initial q) :
    (history q).length ≤ P.dim (base q) + 3 - initial (base q) := by
  unfold Valid coordinate at hv
  omega

theorem frame_length_bound (P : BoundedFullWriter.Readers) (initial : List Bool → ℕ)
    (u trace : List Bool) (hv : Valid P initial (frame u trace)) :
    (frame u trace).length ≤ 2 * u.length + 2 + (P.dim u + 3 - initial u) := by
  have H := history_bound P initial (frame u trace) hv
  rw [history_frame, base_frame] at H
  rw [frame_length]
  omega

end LeanCanny.Encoding.CoordinateDoubleAffineTrace

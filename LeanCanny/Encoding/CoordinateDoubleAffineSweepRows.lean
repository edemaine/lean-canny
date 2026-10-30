/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineSweep
public import LeanCanny.Encoding.FlatAffineBranchCanonicalAncestorMatch
public import LeanCanny.Encoding.FlatAffineEndpointCanonicalParent

/-! # Native swept coordinates, actual height rows, and decreasing slice ranks

Every coordinate index, row index, and ancestor filter is computed from the
original source readers. Advancing a nonterminal newest objective strictly
decreases the number of coordinates remaining for geometric recursion.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineSweep
open LeanCanny.Algebra LeanCanny.Computation
open FlatAffineFullSourceTower (stage)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def coordinate (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) : Fin (P.dim u + 4) :=
  CoordinateAffineTower.selected P old u (depth u)

theorem coordinate_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) :
    UnaryFn (fun u => (coordinate P depth old u).val) := by
  have HQ : (fun u => stage u (depth u)) ∈ FP := mem_FP_pair id_mem_FP (BinaryFn.ofUnary hd).bits_mem_FP
  exact (ho.comp HQ).min (hP.dim.add (UnaryFn.const 3))

noncomputable def height (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ)
    (level : List Bool → List Bool) := FlatAffineLastHeightRow.row (inputs P depth old level) (coordinate P depth old)

theorem height_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    UnaryFn (fun u => (height P depth old level u).val) :=
  FlatAffineLastHeightRow.row_unary (access hP hd ho hl hA) _ (coordinate_unary hP hd ho)

def rank (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) : ℕ :=
  P.dim u + 3 - (coordinate P depth old u).val

theorem rank_unary {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} (hd : UnaryFn depth) (ho : UnaryFn old) : UnaryFn (rank P depth old) :=
  (hP.dim.add (UnaryFn.const 3)).sub (coordinate_unary hP hd ho)

theorem rank_zero_iff (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool) :
    rank P depth old u = 0 ↔ P.dim u + 3 ≤ old (stage u (depth u)) := by
  change P.dim u + 3 - min (old (stage u (depth u))) (P.dim u + 3) = 0 ↔ _
  omega

theorem rank_decreases (P : BoundedFullWriter.Readers) (depth old : List Bool → ℕ) (u : List Bool)
    (hn : old (stage u (depth u)) < P.dim u + 3) :
    rank P depth (objective depth old) u < rank P depth old u := by
  unfold rank coordinate
  rw [newest_selected P depth old u hn]
  change P.dim u + 3 - (old (stage u (depth u)) + 1) <
    P.dim u + 3 - min (old (stage u (depth u))) (P.dim u + 3)
  omega

theorem branch_filter_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    FlatAffineBranchCanonicalAncestorMatch.language (inputs P depth old level) (cone P depth old level)
      (coordinate P depth old) ∈ PSPACE :=
  FlatAffineBranchCanonicalAncestorMatch.mem_PSPACE (access hP hd ho hl hA) _ _ (coordinate_unary hP hd ho)

theorem endpoint_filter_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {depth old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn depth) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    FlatAffineEndpointCanonicalParent.language (inputs P depth old level) (cone P depth old level)
      (coordinate P depth old) ∈ PSPACE :=
  FlatAffineEndpointCanonicalParent.mem_PSPACE (access hP hd ho hl hA) _ _ (coordinate_unary hP hd ho)

end LeanCanny.Encoding.CoordinateDoubleAffineSweep

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.CoordinateDoubleAffineTraceBounds
public import LeanCanny.Connectivity.CoordinateDoubleAffineTerminalConnectivity

/-! # Native terminal connectivity in the shared-source history family

The original readers supply one terminal algorithm over every history.
Its terminal flag is exactly rank zero. The existing validated semantics
include whole-slice connectivity and paths between labeled slice points.
-/

@[expose] public section
namespace LeanCanny.Connectivity.CoordinateDoubleAffineTraceTerminal
open LeanCanny.Encoding LeanCanny.Computation
open CoordinateDoubleAffineTrace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] objective levels depth seedCoordinate

noncomputable def connectedLanguage (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  CoordinateDoubleAffineTerminalConnectivity.language (readers P) (depth d) (objective d old) (levels P d old level)

noncomputable def reachableLanguage (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ)
    (level : List Bool → List Bool) : Language :=
  CoordinateDoubleAffineTerminalReachability.language (readers P) (depth d) (objective d old) (levels P d old level)

theorem connected_decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (connectedLanguage P d old level) :=
  CoordinateDoubleAffineTerminalConnectivity.decider (readers_polyTime hP) (depth_unary hd) (objective_unary hd ho)
    (levels_evaluator hP hd ho hl) (fun q => hA (base q))

theorem reachable_decider {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    SpaceDecider (reachableLanguage P d old level) :=
  CoordinateDoubleAffineTerminalReachability.decider (readers_polyTime hP) (depth_unary hd) (objective_unary hd ho)
    (levels_evaluator hP hd ho hl) (fun q => hA (base q))

theorem connected_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    connectedLanguage P d old level ∈ PSPACE := (connected_decider hP hd ho hl hA).mem_PSPACE

theorem reachable_mem_PSPACE {P : BoundedFullWriter.Readers} (hP : P.PolyTime)
    {d old : List Bool → ℕ} {level : List Bool → List Bool}
    (hd : UnaryFn d) (ho : UnaryFn old) (hl : SpaceFunction level)
    (hA : ∀ u, (LeanCanny.ETR.TermView.term (P.source u)).arity ≤ P.dim u) :
    reachableLanguage P d old level ∈ PSPACE := (reachable_decider hP hd ho hl hA).mem_PSPACE

theorem connected_terminal_iff (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (q : List Bool) :
    CoordinateDoubleAffineTerminalConnectivity.terminal (readers P) (depth d) (objective d old) q ↔
      rank P (seedCoordinate d old) (LeanCanny.pairFst q) = 0 := by
  unfold CoordinateDoubleAffineTerminalConnectivity.terminal
  rw [objective_current]
  change P.dim (base (LeanCanny.pairFst q)) + 3 ≤ coordinate (seedCoordinate d old) (LeanCanny.pairFst q) ↔ _
  unfold rank
  omega

theorem reachable_terminal_iff (P : BoundedFullWriter.Readers) (d old : List Bool → ℕ) (q : List Bool) :
    CoordinateDoubleAffineTerminalReachability.terminal (readers P) (depth d) (objective d old) q ↔
      rank P (seedCoordinate d old) (CoordinateDoubleAffineTerminalReachability.source q) = 0 := by
  unfold CoordinateDoubleAffineTerminalReachability.terminal
  rw [objective_current]
  change P.dim (base (CoordinateDoubleAffineTerminalReachability.source q)) + 3 ≤
    coordinate (seedCoordinate d old) (CoordinateDoubleAffineTerminalReachability.source q) ↔ _
  unfold rank
  omega

end LeanCanny.Connectivity.CoordinateDoubleAffineTraceTerminal

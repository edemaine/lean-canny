/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedBackend
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedRuleMetadata
public import LeanCanny.Algebra.IntegralMixedCommandHeaderWriter
/-! # Literal supplied-mask command headers use original syntax metadata only -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open IntegralMixedCommandHeaderBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure KindAccess (P : Parameters) {F : Inputs} (D : Description P F) : Prop where
  context : BinaryFn (fun root => kindContext (D.kind root))
  coordinate : BinaryFn (fun root => kindCoordinate (D.kind root))
  choice : BinaryFn (fun root => kindChoice (D.kind root))
  rawTag : BinaryFn (fun root => kindRawTag (D.kind root))
  degree : BinaryFn D.degree

noncomputable def coarseHeader {F : Inputs} (S : FlatAffineExceptionalSuppliedRules.Source F) (root : List Bool) : Header :=
  ⟨1, (FlatAffineExceptionalSuppliedRules.coarse S root).coordinate %
      (F.source.dim (S.input root) + 3 - (FlatAffineExceptionalSuppliedRules.coarse S root).offset.val + 1),
    (FlatAffineExceptionalSuppliedRules.coarse S root).offset.val,
    (FlatAffineExceptionalSuppliedRules.coarse S root).objective, 0, 0, 1⟩

theorem coarse_free_unary {F : Inputs} (hF : F.Access) (S : FlatAffineExceptionalSuppliedRules.Source F)
    (hS : FlatAffineExceptionalSuppliedRules.Access S) :
    UnaryFn (fun root => F.source.dim (S.input root) + 3 - (FlatAffineExceptionalSuppliedRules.coarse S root).offset.val + 1) := by
  have HA : UnaryFn (fun root => F.source.dim (S.input root) + 3) :=
    (((FlatAffineFullSourceTower.arity_unary hF).comp hS.input).sub (UnaryFn.const 1)).of_eq (fun root => by unfold arity; omega)
  have HO : UnaryFn (fun root => (FlatAffineExceptionalSuppliedRules.coarse S root).offset.val) :=
    (FlatAffineExceptionalSuppliedRules.coarseOffset_unary hF S hS).of_eq (fun root => FlatAffineExceptionalSuppliedRules.coarseOffset_eq S root)
  exact (HA.sub HO).add (UnaryFn.const 1)

theorem coarseHeader_readers {F : Inputs} (hF : F.Access) (S : FlatAffineExceptionalSuppliedRules.Source F)
    (hS : FlatAffineExceptionalSuppliedRules.Access S) : Readers (coarseHeader S) := by
  have HC : BinaryFn (fun root => (FlatAffineExceptionalSuppliedRules.coarse S root).coordinate) :=
    (FlatAffineExceptionalSuppliedRules.coarseObjective_binary hF S hS).of_eq (fun _ => rfl)
  exact { context := BinaryFn.const 1
          coordinate := HC.mod (BinaryFn.ofUnary (coarse_free_unary hF S hS))
          offset := (BinaryFn.ofUnary (FlatAffineExceptionalSuppliedRules.coarseOffset_unary hF S hS)).of_eq
            (fun root => FlatAffineExceptionalSuppliedRules.coarseOffset_eq S root)
          objective := FlatAffineExceptionalSuppliedRules.coarseObjective_binary hF S hS
          degree := BinaryFn.const 0
          choice := BinaryFn.const 0
          rawTag := BinaryFn.const 1 }

noncomputable def cutHeader (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :=
  IntegralMixedCommandHeaderBits.selection (chosen P D root)

theorem cutHeader_readers (P : Parameters) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hK : KindAccess P D) : Readers (cutHeader P D) :=
  { context := hK.context
    coordinate := hK.coordinate
    offset := (BinaryFn.ofUnary (FlatAffineExceptionalSuppliedRules.offset_unary hF D.source hS)).of_eq
      (fun root => FlatAffineExceptionalSuppliedRules.offset_eq D.source root)
    objective := FlatAffineExceptionalSuppliedRules.objective_binary hF D.source hS
    degree := hK.degree
    choice := hK.choice
    rawTag := hK.rawTag }

theorem coarseHeader_command (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :
    coarseHeader D.source root = command (P := D.base.spatial root) (B := (parameters P D.source).width root)
      (.critical (FlatAffineExceptionalSuppliedRules.coarse D.source root)) := rfl

theorem cutHeader_command (P : Parameters) {F : Inputs} (D : Description P F) (root : List Bool) :
    cutHeader P D root = command (.cut (FlatAffineExceptionalSuppliedRules.sweep D.source D.cone root) (D.kind root) (D.degree root)
      (D.degree_bound root) ((D.degree_bound root).trans (D.base.scalar_cap root))) := rfl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData

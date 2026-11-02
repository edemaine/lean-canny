/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedSnapshot
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedHeaderTables
/-! # Original-only scalar controls of the actual total advice-root history

Only original source access and native written syntax metadata are charged.
Every affine cell, scale, initial-Q slope and full/physical header reader is
constructed for all words of the decoded Data, including malformed advice.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem scalar_controls (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length))
    (hK : KindAccess P D) (hl : ∀ root, (D.base.spatial root).leading = 1) :
    IntegralMixedFullScalarBits.Controls (parameters P D.source) (backend P D) :=
  IntegralMixedSuppliedScalarBits.controls (parameters P D.source) (parameters_access P a hF D.source hS)
    (backend P D) hF (layout P D) (layout_access P a hF D hS hn) D.cone (physicalDouble P D) (fun _ => true)
    (physicalDouble_FP P a hF D hS hn) (constFn_mem_FP [true]) (snapshot P D hl)
    (fullMetadata P a hF D hS hn hK) (physicalMetadata P a hF D hS hn hK)
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData

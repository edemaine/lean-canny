/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedBackend
/-! # Native syntax layout for every task of the supplied-mask history -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def criticalAt (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) : Prop :=
  IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source) (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q) =
    (D.base.rules (RankedHistoryTask.root q)).length
instance (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) : Decidable (criticalAt P D q) := inferInstanceAs (Decidable (_ = _))

theorem criticalAt_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length)) : FPPred (criticalAt P D) := by
  have ap := parameters_access P a hF D.source hS
  have HB : BinaryFn (fun q => IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source) (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)) :=
    (BinaryFn.ofUnary (IntegralMixedFullHistoryFamilyBits.prefix_unary (parameters P D.source) ap)).comp
      (IntegralMixedVirtualTaskBits.saved_FP (parameters P D.source) ap)
  have HN : BinaryFn (fun q => (D.base.rules (RankedHistoryTask.root q)).length) := (BinaryFn.ofUnary hn).comp RankedHistoryTask.root_FP
  exact HB.eq HN

noncomputable def layout (P : Parameters) {F : Inputs} (D : Description P F) : FlatAffineExceptionalSuppliedRecipe.Layout F where
  input q := D.source.input (RankedHistoryTask.root q)
  height := D.source.height
  mode q := if get (parameters P D.source) .slot8 q < arity F (D.source.input (RankedHistoryTask.root q)) then
    if get (parameters P D.source) .slot15 q = 1 then if criticalAt P D q then 2 else 0 else 1 else 0
  row q := ⟨get (parameters P D.source) .slot8 q % arity F (D.source.input (RankedHistoryTask.root q)), Nat.mod_lt _ (by unfold arity; omega)⟩
  sweep _ := true
  mask q := FlatAffineExceptionalSuppliedRules.maskWord D.source (RankedHistoryTask.root q)

theorem layout_access (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length)) :
    FlatAffineExceptionalSuppliedRecipe.Access (layout P D) := by
  have ap := parameters_access P a hF D.source hS
  have HI := mem_FP_comp RankedHistoryTask.root_FP hS.input
  have HN := (FlatAffineFullSourceTower.arity_unary hF).comp HI
  have HH := get_binary (parameters P D.source) ap .slot8
  have HC := (get_binary (parameters P D.source) ap .slot15).eq (BinaryFn.const 1)
  have HM := BinaryFn.ite (HH.lt (BinaryFn.ofUnary HN))
    (BinaryFn.ite HC (BinaryFn.ite (criticalAt_FP P a hF D hS hn) (BinaryFn.const 2) (BinaryFn.const 0)) (BinaryFn.const 1)) (BinaryFn.const 0)
  exact { input := HI
          height := hS.height
          mode := HM
          row := HH.mod (BinaryFn.ofUnary HN)
          sweep := constFn_mem_FP [true]
          mask := mem_FP_comp (f := RankedHistoryTask.root) (g := FlatAffineExceptionalSuppliedRules.maskWord D.source) RankedHistoryTask.root_FP (FlatAffineExceptionalSuppliedRules.maskWord_FP hF D.source hS) }

theorem layout_frozen (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) :
    FlatAffineExceptionalSuppliedRecipe.frozen (layout P D) q = FlatAffineExceptionalSuppliedRules.frozen D.source (RankedHistoryTask.root q) := by
  change SuppliedFrozenMaskBits.selected _ (FlatAffineExceptionalSuppliedRules.maskWord D.source (RankedHistoryTask.root q)) = _
  rw [FlatAffineExceptionalSuppliedRules.maskWord_eq, SuppliedFrozenMaskBits.selected_mask]

theorem layout_order (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) :
    FlatAffineExceptionalSuppliedRecipe.order (layout P D) q = FlatAffineExceptionalSuppliedRules.order D.source (RankedHistoryTask.root q) :=
  congrArg LeanCanny.Geometry.FrozenCoordinateOrdering.permutation (layout_frozen P D q)

theorem layout_coarseOrder (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) :
    FlatAffineExceptionalSuppliedRecipe.coarseOrder (layout P D) q = FlatAffineExceptionalSuppliedRules.coarseOrder D.source (RankedHistoryTask.root q) := by
  change LeanCanny.Geometry.FrozenCoordinateOrdering.permutation ((FlatAffineExceptionalSuppliedRecipe.frozen (layout P D) q).erase _) = _
  rw [layout_frozen]
  rfl
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData

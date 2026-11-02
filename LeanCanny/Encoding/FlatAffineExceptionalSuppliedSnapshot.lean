/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedAffineCells
/-! # Literal scalar snapshots of the actual total supplied-mask backend -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def physicalDouble (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) := decide (criticalAt P D q)

theorem physicalDouble_FP (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access) (D : Description P F)
    (hS : FlatAffineExceptionalSuppliedRules.Access D.source) (hn : UnaryFn (fun root => (D.base.rules root).length)) :
    (fun q => [physicalDouble P D q]) ∈ FP := (criticalAt_FP P a hF D hS hn).flag_mem_FP

theorem snapshot (P : Parameters) {F : Inputs} (D : Description P F)
    (hl : ∀ root, (D.base.spatial root).leading = 1) :
    IntegralMixedSuppliedScalarBits.Snapshot (parameters P D.source) (backend P D) (layout P D) D.cone (physicalDouble P D) (fun _ => true) where
  leading := hl
  physicalScales := by
    intro q i
    change ((IntegralMixedHeightCellsBits.physicalFamily (parameters P D.source) (backend P D)).rule
      (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)).scales i = _
    rw [physical_rule_backend]
    have HE := congrArg (fun root => (D.base.rules root).length)
      (IntegralMixedFullHistoryFamilyBits.saved_root (parameters P D.source) q)
    have HB : (IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source)
        (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q) =
        (D.base.rules (pairFst (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q))).length) ↔ criticalAt P D q := by
      unfold criticalAt
      rw [HE]
    by_cases hc : criticalAt P D q
    · rw [ite_eq_left (HB.mpr hc)]
      change (2 : ℤ) = _
      simp only [physicalDouble, hc, decide_true, ite_true]
    · rw [ite_eq_right (fun hh => hc (HB.mp hh))]
      change (1 : ℤ) = _
      simp only [physicalDouble, hc, decide_false, Bool.false_eq_true, ite_false]
  virtualScales := by
    intro q i
    change ((IntegralMixedFullHistoryFamilyBits.family (parameters P D.source) (backend P D)).rule
      (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)).critical.scales i = _
    rw [virtual_rule_backend]
    rfl
  height := by
    intro q
    change ((IntegralMixedFullHistoryFamilyBits.family (parameters P D.source) (backend P D)).rule
      (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)).height.val =
        ((FlatAffineExceptionalSuppliedRecipe.order (layout P D) q).symm (D.source.height (D.source.input (RankedHistoryTask.root q)))).val
    calc
      _ = (FlatAffineExceptionalSuppliedRules.sweep D.source D.cone
          (pairFst (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q))).height.val :=
        congrArg (fun r => (IntegralMixedCriticalSweep.Rule.height r).val) (virtual_rule_backend P D (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q))
      _ = (FlatAffineExceptionalSuppliedRules.sweep D.source D.cone (RankedHistoryTask.root q)).height.val :=
        congrArg (fun root => (FlatAffineExceptionalSuppliedRules.sweep D.source D.cone root).height.val)
          (IntegralMixedFullHistoryFamilyBits.saved_root (parameters P D.source) q)
      _ = _ := by rw [layout_order]; rfl
  slope := by
    intro q
    change ((IntegralMixedFullHistoryFamilyBits.family (parameters P D.source) (backend P D)).rule
      (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)).slope =
        FlatAffineExceptionalBankSource.denominator F D.cone D.source.height (D.source.input (RankedHistoryTask.root q))
    calc
      _ = (FlatAffineExceptionalSuppliedRules.sweep D.source D.cone
          (pairFst (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q))).slope :=
        congrArg IntegralMixedCriticalSweep.Rule.slope (virtual_rule_backend P D (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q))
      _ = _ := congrArg (fun root => FlatAffineExceptionalBankSource.denominator F D.cone D.source.height (D.source.input root))
        (IntegralMixedFullHistoryFamilyBits.saved_root (parameters P D.source) q)
  affine := affine_backend P D

end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData

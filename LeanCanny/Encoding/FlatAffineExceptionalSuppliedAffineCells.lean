/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedLayout
/-! # Natural affine row snapshots avoid dependent root transports -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def affineAt {n : ℕ} (r : CriticalRule n) (i : ℕ) : AffineExpr :=
  if hi : i < n + 1 then r.heights ⟨i, hi⟩ else .constant 0
noncomputable def coarseAffine {F : Inputs} (D : FlatAffineExceptionalSuppliedRules.Source F) (root : List Bool) (i : ℕ) :=
  affineAt (FlatAffineExceptionalSuppliedRules.coarse D root) i
noncomputable def virtualAffine {F : Inputs} (D : FlatAffineExceptionalSuppliedRules.Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (FlatAffineCompleteRootStages.next F)) (root : List Bool) (i : ℕ) :=
  affineAt (FlatAffineExceptionalSuppliedRules.sweep D C root).critical i

theorem affineAt_default (n i : ℕ) : affineAt (IntegralMixedFullPhysicalBits.defaultRule n) i = .constant 0 := by
  unfold affineAt
  split_ifs <;> rfl

theorem affine_rule_backend (P : Parameters) {F : Inputs} (D : Description P F) (key : List Bool) (i : ℕ) :
    affineAt (IntegralMixedHeightCellsBits.rule (parameters P D.source) (backend P D) key) i =
      if IntegralMixedHeightCellsBits.context key = 1 then
        if IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P D.source) key = (D.base.rules (pairFst key)).length then
          coarseAffine D.source (pairFst key) i else .constant 0
      else virtualAffine D.source D.cone (pairFst key) i := by
  unfold IntegralMixedHeightCellsBits.rule
  by_cases hc : IntegralMixedHeightCellsBits.context key = 1
  · rw [ite_eq_left hc, ite_eq_left hc, physical_rule_backend]
    split_ifs
    · rfl
    · exact affineAt_default _ _
  · rw [ite_eq_right hc, ite_eq_right hc, virtual_rule_backend]
    rfl

attribute [local irreducible] coarseAffine virtualAffine

theorem affine_backend (P : Parameters) {F : Inputs} (D : Description P F) (q : List Bool) :
    IntegralMixedHeightCellsBits.affine (parameters P D.source) (backend P D) q =
      FlatAffineExceptionalSuppliedRecipe.expression (layout P D) q := by
  change affineAt (IntegralMixedHeightCellsBits.rule (parameters P D.source) (backend P D)
    (IntegralMixedVirtualTaskBits.saved (parameters P D.source) q)) (get (parameters P D.source) .slot8 q) = _
  rw [affine_rule_backend]
  simp only [IntegralMixedHeightCellsBits.context_saved, IntegralMixedFullHistoryFamilyBits.saved_root]
  rw [congrArg (fun root => (D.base.rules root).length) (IntegralMixedFullHistoryFamilyBits.saved_root (parameters P D.source) q)]
  change (if get (parameters P D.source) .slot15 q = 1 then
    if criticalAt P D q then coarseAffine D.source (RankedHistoryTask.root q) (get (parameters P D.source) .slot8 q) else .constant 0
    else virtualAffine D.source D.cone (RankedHistoryTask.root q) (get (parameters P D.source) .slot8 q)) = _
  by_cases hi : get (parameters P D.source) .slot8 q < arity F (D.source.input (RankedHistoryTask.root q))
  · have HR : (layout P D).row q = ⟨get (parameters P D.source) .slot8 q, hi⟩ := Fin.ext (Nat.mod_eq_of_lt hi)
    by_cases hc : get (parameters P D.source) .slot15 q = 1
    · rw [ite_eq_left hc]
      by_cases hb : criticalAt P D q
      · rw [ite_eq_left hb]
        have HM : (layout P D).mode q = 2 := by simp only [layout, hi, hc, hb, ite_true]
        rw [FlatAffineExceptionalSuppliedRecipe.expression, ite_eq_right (by omega), ite_eq_left HM, layout_coarseOrder, HR]
        unfold coarseAffine affineAt
        have HB : get (parameters P D.source) .slot8 q < F.source.dim (D.source.input (RankedHistoryTask.root q)) + 3 + 1 := by unfold arity at hi; omega
        rw [dite_eq_left HB]
        rfl
      · rw [ite_eq_right hb]
        have HM : (layout P D).mode q = 0 := by simp only [layout, hi, hc, hb, ite_true, ite_false]
        rw [FlatAffineExceptionalSuppliedRecipe.expression, ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right hc]
      have HM : (layout P D).mode q = 1 := by simp only [layout, hi, hc, ite_true, ite_false]
      rw [FlatAffineExceptionalSuppliedRecipe.expression, ite_eq_left HM, layout_order, HR]
      unfold virtualAffine affineAt
      have HB : get (parameters P D.source) .slot8 q < F.source.dim (D.source.input (RankedHistoryTask.root q)) + 3 + 1 := by unfold arity at hi; omega
      rw [dite_eq_left HB]
      rfl
  · have HM : (layout P D).mode q = 0 := by simp only [layout, hi, ite_false]
    have HE : FlatAffineExceptionalSuppliedRecipe.expression (layout P D) q = .constant 0 := by
      rw [FlatAffineExceptionalSuppliedRecipe.expression, ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [HE]
    have HB : ¬get (parameters P D.source) .slot8 q < F.source.dim (D.source.input (RankedHistoryTask.root q)) + 3 + 1 := by unfold arity at hi; omega
    have HC0 : coarseAffine D.source (RankedHistoryTask.root q) (get (parameters P D.source) .slot8 q) = .constant 0 := by
      unfold coarseAffine affineAt
      rw [dite_eq_right HB]
    have HV0 : virtualAffine D.source D.cone (RankedHistoryTask.root q) (get (parameters P D.source) .slot8 q) = .constant 0 := by
      unfold virtualAffine affineAt
      rw [dite_eq_right HB]
    rw [HC0, HV0]
    split_ifs <;> rfl

end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData

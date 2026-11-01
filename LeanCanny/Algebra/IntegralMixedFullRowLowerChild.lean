/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowNative
public import LeanCanny.Algebra.IntegralMixedVirtualSpatialModel

/-! # Full-row lower tasks retain the actual virtual source snapshot -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowLowerChild
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedFullRowTasks
open scoped Classical

theorem task_family (P : Parameters) (F : Family) (h : RootGeometry P F)
    (p : Phase) (x : ℕ) (q : List Bool) :
    IntegralMixedVirtualSnapshotBits.family P F (taskAt P F p x q) =
      IntegralMixedVirtualSnapshotBits.sourceAt F (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot13 q) (get P .coefficient q) (lowTarget P F q) (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q) := by
  unfold IntegralMixedVirtualSnapshotBits.family
  simp only [task_saved, task_get, reduceCtorEq, ite_false, ite_true,
    min_eq_left (IntegralMixedFullRowTaskBounds.lowTarget_cap P F h (width P F) q)]
  apply IntegralMixedVirtualSnapshotBits.sourceAt_modulus
  exact task_modulus P F p x q

theorem frozen_child (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (he : equation P F q) :
    IntegralMixedVirtualSnapshotBits.frozenLower P F (taskAt P F .frozenLower 0 q) =
      IntegralMixedFullRowRequest.lowValue (family P F) (indices P F) (width P F) q := by
  unfold IntegralMixedVirtualSnapshotBits.frozenLower IntegralMixedVirtualSnapshotBits.eulerAt
  rw [task_family P F h]
  unfold IntegralMixedFullRowRequest.lowValue IntegralMixedFullRowMultiplier.low
  rw [ite_eq_left he]
  rfl

theorem gradient_child (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (he : ¬ equation P F q) :
    IntegralMixedVirtualSpatialBits.cleared P F (taskAt P F .clearedGridSum 1 q) =
      IntegralMixedFullRowRequest.lowValue (family P F) (indices P F) (width P F) q := by
  have HF := task_fields P F h .clearedGridSum 1 (by decide) q
  rw [IntegralMixedVirtualSpatialBits.cleared_derivative P F _ HF.2.2]
  have HG : IntegralMixedVirtualSpatialBits.gradientAt F
      (IntegralMixedVirtualTaskBits.saved P (taskAt P F .clearedGridSum 1 q))
      (get P .derivative (taskAt P F .clearedGridSum 1 q)) (get P .target (taskAt P F .clearedGridSum 1 q))
      (get P .row (taskAt P F .clearedGridSum 1 q)) (get P .col (taskAt P F .clearedGridSum 1 q))
      (modulus P (taskAt P F .clearedGridSum 1 q)) (modulus_ne_zero P _) =
      IntegralMixedVirtualSpatialBits.gradientAt F (IntegralMixedVirtualTaskBits.saved P q)
        ((indices P F).coordinate q).val (lowTarget P F q) (get P .row q) (get P .col q)
        (modulus P q) (modulus_ne_zero P q) := by
    apply IntegralMixedVirtualSpatialBits.gradient_congr
    · exact task_saved P F .clearedGridSum 1 q
    · exact HF.2.1
    · exact HF.1
    · simp only [task_get, reduceCtorEq, ite_false]
    · simp only [task_get, reduceCtorEq, ite_false]
    · exact task_modulus P F .clearedGridSum 1 q
  rw [HG]
  let j : Fin ((IntegralMixedVirtualTaskBits.arithmetic P F).free q) :=
    ⟨((indices P F).coordinate q).val, by
      change ((indices P F).coordinate q).val < (family P F).ambient q - ((family P F).rule q).critical.offset.val + 1
      exact ((indices P F).coordinate q).isLt⟩
  have HJ : j.val = ((indices P F).coordinate q).val := rfl
  have HG' := IntegralMixedVirtualSpatialBits.gradient_snapshot P F q j (lowTarget P F q)
  rw [HJ] at HG'
  rw [← HG']
  rw [IntegralCriticalGradientBits.packet (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient q j]
  unfold IntegralMixedFullRowRequest.lowValue IntegralMixedFullRowMultiplier.low
  rw [ite_eq_right he]
  rfl

noncomputable def model (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if equation P F q then IntegralMixedVirtualSnapshotBits.frozenLower P F (lowTask P F q)
  else IntegralMixedVirtualSpatialBits.cleared P F (lowTask P F q)

theorem model_eq (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool) :
    model P F q = IntegralMixedFullRowRequest.lowValue (family P F) (indices P F) (width P F) q := by
  unfold model lowTask
  split_ifs with H
  · exact frozen_child P F h q H
  · exact gradient_child P F h q H

end LeanCanny.Algebra.IntegralMixedFullRowLowerChild

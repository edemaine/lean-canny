/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextLowerModel
/-! # Current virtual frozen and Euler replies from actual component matches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextLowerReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualNativeLowerBits
open IntegralMixedVirtualContextBits IntegralMixedVirtualContextLowerModelBits
set_option backward.isDefEq.respectTransparency false

structure Callbacks (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop extends IntegralMixedVirtualContextReplyBits.Callbacks P F reply where
  leading : ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → IntegralMixedVirtualContextBits.context P q →
    reply (IntegralMixedScalarQueryBits.originalLeading P q) = IntegralMixedVirtualContextBits.originalLeadingValue P F q

theorem context (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (q c : List Bool)
    (hroot : RankedHistoryTask.root c = RankedHistoryTask.root q) (hbirth : birth P c = birth P q)
    (hroutine : IntegralMixedRoutineTaskBits.routine P c = IntegralMixedRoutineTaskBits.routine P q)
    (hcontext : get P .slot15 c = get P .slot15 q)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : IntegralMixedVirtualContextBits.context P q) (hc : isPhase p c) : reply c = component P F p c :=
  hm p c hp (IntegralMixedVirtualContextReplyBits.current_selected P p q c hroot hbirth hroutine hcontext hv hr hx hc)

theorem matrix (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    reply (IntegralCriticalFlatMatrixQuery.writer P p z) = component P F p (IntegralCriticalFlatMatrixQuery.writer P p z) :=
  hm p _ hp (IntegralMixedVirtualContextReplyBits.matrix_selected P p z hv hr hx)

theorem next (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hx : IntegralMixedVirtualContextBits.context P q) :
    reply (IntegralCriticalFlatEulerBits.next P p q) = component P F p (IntegralCriticalFlatEulerBits.next P p q) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatEulerBits.next_root P p q)
    (IntegralCriticalFlatEulerBits.next_birth P p q) _ (IntegralCriticalFlatEulerBits.next_get P p q .slot15) hv hr hx
    (IntegralCriticalFlatEulerBits.next_phase P p q)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerBits.next_get]

theorem coordinate (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    reply (IntegralCriticalFlatCoordinateQuery.writer P p z) = component P F p (IntegralCriticalFlatCoordinateQuery.writer P p z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatCoordinateQuery.writer_root P p z)
    (IntegralCriticalFlatCoordinateQuery.writer_birth P p z) _
    (IntegralCriticalFlatCoordinateQuery.writer_other P p z .slot15 (by decide)) hv hr hx
    (IntegralCriticalFlatCoordinateQuery.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatCoordinateQuery.writer_other P p z .slot14 (by decide)]

theorem spatial (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 16) (x : ℕ) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : IntegralMixedVirtualContextBits.context P (pairFst z)) :
    reply (IntegralCriticalFlatEulerRowsBits.spatial P p x z) = component P F p (IntegralCriticalFlatEulerRowsBits.spatial P p x z) := by
  apply context P F reply hm p hp _ _ (IntegralCriticalFlatEulerRowsBits.spatial_root P p x z)
    (IntegralCriticalFlatEulerRowsBits.spatial_birth P p x z) _
    (IntegralCriticalFlatEulerRowsBits.spatial_other P p x z .slot15 (by decide) (by decide) (by decide)) hv hr hx
    (IntegralCriticalFlatEulerRowsBits.spatial_phase P p x z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatEulerRowsBits.spatial_other P p x z .slot14 (by decide) (by decide) (by decide)]

theorem frozenPower_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .frozenPowerTerm q = true) : IntegralMixedVirtualContextBits.FrozenPowerRepliesAt P F reply q := by
  intro _ r t
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .frozenPowerTerm q).mp hq).2
  have HQ := (selectedValid_iff P .frozenPowerTerm q).mp (IntegralMixedVirtualContextBits.selected_raw P .frozenPowerTerm q hq)
  exact matrix P F reply hm .clearedHeight (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1) (by simpa only [pairFst_pair] using HX)

theorem frozenSum_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .frozenPowerSum q = true) : IntegralMixedVirtualContextBits.FrozenSumRepliesAt P F reply q := by
  intro i _
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .frozenPowerSum q).mp hq).2
  have HQ := (selectedValid_iff P .frozenPowerSum q).mp (IntegralMixedVirtualContextBits.selected_raw P .frozenPowerSum q hq)
  exact coordinate P F reply hm .frozenPowerTerm (by decide) _ (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1) (by simpa only [pairFst_pair] using HX)

theorem frozenConstant_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (hs : Callbacks P F reply) (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .frozenConstant q = true) : IntegralMixedVirtualContextBits.FrozenConstantRepliesAt P F reply q := by
  intro _
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .frozenConstant q).mp hq).2
  have HQ := (selectedValid_iff P .frozenConstant q).mp (IntegralMixedVirtualContextBits.selected_raw P .frozenConstant q hq)
  exact ⟨hs.leading q HQ.1 HQ.2.1 HX, next P F reply hm .frozenPowerSum (by decide) q HQ.1 HQ.2.1 HX⟩

theorem frozenLower_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .frozenLower q = true) : IntegralMixedVirtualContextBits.FrozenLowerRepliesAt P F reply q := by
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .frozenLower q).mp hq).2
  have HQ := (selectedValid_iff P .frozenLower q).mp (IntegralMixedVirtualContextBits.selected_raw P .frozenLower q hq)
  refine ⟨?_, next P F reply hm .frozenConstant (by decide) q HQ.1 HQ.2.1 HX⟩
  unfold IntegralCriticalFlatFrozenLowerBits.clearedTask
  exact spatial P F reply hm .clearedGridSum (by decide) 0 _
    (by simpa only [pairFst_pair] using HQ.1) (by simpa only [pairFst_pair] using HQ.2.1) (by simpa only [pairFst_pair] using HX)

theorem coordinate_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .coordinateGradientProduct q = true) : IntegralMixedVirtualContextBits.CoordinateRepliesAt P F reply q := by
  intro _
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .coordinateGradientProduct q).mp hq).2
  have HQ := (selectedValid_iff P .coordinateGradientProduct q).mp (IntegralMixedVirtualContextBits.selected_raw P .coordinateGradientProduct q hq)
  have HO : pairFst (IntegralMixedVirtualContextBits.coordinateQuery P F q) = q := IntegralCriticalFlatEulerRowsBits.productGradientQuery_parent P (source P F) q
  change reply (IntegralCriticalFlatEulerRowsBits.spatial P .clearedGridSum 1 (IntegralMixedVirtualContextBits.coordinateQuery P F q)) = _
  exact spatial P F reply hm .clearedGridSum (by decide) 1 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1) (by rw [HO]; exact HX)

theorem sum_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .eulerSum q = true) : IntegralMixedVirtualContextBits.SumRepliesAt P F reply q := by
  intro i _
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .eulerSum q).mp hq).2
  have HQ := (selectedValid_iff P .eulerSum q).mp (IntegralMixedVirtualContextBits.selected_raw P .eulerSum q hq)
  unfold IntegralCriticalFlatEulerRowsBits.sumTask
  have HO : pairFst (IntegralEulerBits.termQuery (source P F) (pair q (BinaryNatCode.encode i))) = q := by
    simp only [IntegralEulerBits.termQuery, pairFst_pair]
  exact spatial P F reply hm .coordinateGradientProduct (by decide) 0 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1) (by rw [HO]; exact HX)

theorem objective_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .eulerObjective q = true) : IntegralMixedVirtualContextBits.ObjectiveRepliesAt P F reply q := by
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .eulerObjective q).mp hq).2
  have HQ := (selectedValid_iff P .eulerObjective q).mp (IntegralMixedVirtualContextBits.selected_raw P .eulerObjective q hq)
  exact ⟨next P F reply hm .frozenLower (by decide) q HQ.1 HQ.2.1 HX,
    next P F reply hm .eulerSum (by decide) q HQ.1 HQ.2.1 HX⟩

theorem lower_current (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedVirtualContextBits.selected P .eulerLower q = true) : IntegralMixedVirtualContextBits.LowerRepliesAt P F reply q := by
  have HX := ((IntegralMixedVirtualContextBits.selected_iff P .eulerLower q).mp hq).2
  have HQ := (selectedValid_iff P .eulerLower q).mp (IntegralMixedVirtualContextBits.selected_raw P .eulerLower q hq)
  refine ⟨fun _ => next P F reply hm .eulerObjective (by decide) q HQ.1 HQ.2.1 HX, ?_⟩
  intro _
  have HO : pairFst (IntegralMixedVirtualContextBits.gradientQuery P F q) = q := pairFst_pair _ _
  exact spatial P F reply hm .clearedGridSum (by decide) 1 _ (by rw [HO]; exact HQ.1) (by rw [HO]; exact HQ.2.1) (by rw [HO]; exact HX)

theorem frozenPower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.frozenPowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.frozenPower_correct P a F h g reply (frozenPower_current P F reply hm)

theorem frozenSum_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.frozenSumMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.frozenSum_correct P a F h g reply (frozenSum_current P F reply hm)

theorem frozenConstant_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) (hs : Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.frozenConstantMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.frozenConstant_correct P a F h reply (frozenConstant_current P F reply hm hs)

theorem frozenLower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.frozenLowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.frozenLower_correct P a F h reply (frozenLower_current P F reply hm)

theorem coordinate_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.coordinateMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.coordinate_correct P a F h g reply (coordinate_current P F reply hm)

theorem sum_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.sumMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.sum_correct P a F h g reply (sum_current P F reply hm)

theorem objective_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.objectiveMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.objective_correct P a F h reply (objective_current P F reply hm)

theorem lower_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedVirtualContextBits.lowerMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedVirtualContextBits.lower_correct P a F h reply (lower_current P F reply hm)

end LeanCanny.Algebra.IntegralMixedVirtualContextLowerReplyBits

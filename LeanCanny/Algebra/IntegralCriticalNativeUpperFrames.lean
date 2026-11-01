/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeUpperReplies
/-! # Native upper requests keep their root, word budget and strict rank -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relative relativeAccess reduction reductionAccess characteristic characteristicAccess
  IntegralCriticalTotalCreatingBits.atFamily

theorem frame_of_tasks (F : Scripts) (q c : List Bool) (ht : Tasks F.toParameters q c)
    (hr : rank F.toParameters c < rank F.toParameters q) : Frame F q c := by
  rcases ht with rfl | ht
  · exact False.elim (Nat.lt_irrefl _ hr)
  · exact ⟨ht.1, ht.2, hr⟩

theorem frame17 (F : Scripts) (h : Controls F) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .reductionEntry q)
    (hc : (IntegralCriticalFlatReductionEntryBits.program F.toParameters (relative F) (relativeAccess F h)).controller.Requests reply budget q c) : Frame F q c :=
  frame_of_tasks F q c
    (IntegralCriticalFlatReductionEntryBits.requests_tasks _ _ _ reply budget q q c (tasks_self _ _) hc)
    (IntegralCriticalFlatReductionEntryBits.requests_rank _ _ _ reply budget q c hp hc)

theorem frame19 (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .actionEntry q)
    (hc : (IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).controller.Requests reply budget q c) : Frame F q c :=
  frame_of_tasks F q c
    (IntegralCriticalFlatActionBits.requests_tasks _ _ reply budget q q c (tasks_self _ _) hc)
    (IntegralCriticalFlatActionBits.requests_rank _ _ reply budget q c hp hc)

theorem frame21 (F : Scripts) (h : Controls F) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .momentEntry q)
    (hc : (IntegralCriticalFlatMomentEntryBits.program F.toParameters h.task.toAccess (characteristic F)
      (characteristicAccess F h)).controller.Requests reply budget q c) : Frame F q c :=
  IntegralCriticalFlatMomentEntryBits.requests_frame _ _ _ _ reply budget q c hp hc

theorem frame23 (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .relativeFactor q)
    (hc : (IntegralCriticalFlatRelativeFactorBits.program F.toParameters (characteristic F)).controller.Requests reply budget q c) : Frame F q c :=
  frame_of_tasks F q c
    (IntegralCriticalFlatRelativeFactorBits.requests_tasks _ _ reply budget q q c (tasks_self _ _) hc)
    (IntegralCriticalFlatRelativeFactorBits.requests_rank _ _ reply budget q c hp hc)

theorem frame25 (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .criticalCoefficient q)
    (hc : (IntegralCriticalFlatActualCoefficientBits.program F).controller.Requests reply budget q c) : Frame F q c :=
  frame_of_tasks F q c
    (IntegralCriticalFlatActualCoefficientBits.requests_tasks F reply budget q q c (tasks_self _ _) hc)
    (IntegralCriticalFlatActualCoefficientBits.requests_rank F reply budget q c hp hc)

theorem frame26 (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ)
    (q c : List Bool) (hp : isPhase .companion q)
    (hc : (IntegralCriticalTotalCompanionBits.program F).controller.Requests reply budget q c) : Frame F q c := by
  obtain ⟨_, _, rfl⟩ := (IntegralCriticalTotalCompanionBits.requests_iff F reply budget q c).mp hc
  refine ⟨?_, IntegralCriticalTotalCompanionBits.child_length F q, IntegralCriticalTotalCompanionBits.child_rank F q hp⟩
  simpa only [IntegralCriticalFlatHeightBits.root] using IntegralCriticalTotalCompanionBits.child_root F q

end LeanCanny.Algebra.IntegralCriticalNativeUpperBits

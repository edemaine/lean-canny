/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
public import LeanCanny.Algebra.IntegralMixedFramedCutSourcePlanning
/-! # Lower-choice probes do not modify the chronological history

Only the selected finite choice is changed in a full-factor source profile.
The old run, source, sweep rule, physical coordinate and coefficient basis
are retained literally. Honest root pullback and planning commute with it.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutChoiceBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

def selection {n : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    (s : IntegralMixedFullHistoryFamilyBits.Selection P) (k : ℕ) : IntegralMixedFullHistoryFamilyBits.Selection P :=
  {s with kind:=IntegralMixedRelativeCuts.atChoice s.rule s.kind k}
noncomputable def profile (P : Parameters) (D : Plan P) (q : IntegralMixedFramedCutSourceBits.Profile P D) (k : ℕ) :
    IntegralMixedFramedCutSourceBits.Profile P D := {q with selection:=selection q.selection k}

theorem profile_root (P : Parameters) (D : Plan P) (q : IntegralMixedFramedCutSourceBits.Profile P D) (k : ℕ) :
    (profile P D q k).root=q.root := rfl
theorem profile_birth (P : Parameters) (D : Plan P) (q : IntegralMixedFramedCutSourceBits.Profile P D) (k : ℕ) :
    (profile P D q k).birth=q.birth := rfl

theorem pullback_profile (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)) (k : ℕ) :
    IntegralMixedFramedCutRootPullback.profile P D project extra
      (profile _ _ q k)=profile P D (IntegralMixedFramedCutRootPullback.profile P D project extra q) k := rfl

theorem planned_profile (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)) (k : ℕ) :
    IntegralMixedFramedCutPlanning.profile P D L F C (profile _ _ q k)=
      profile P D (IntegralMixedFramedCutPlanning.profile P D L F C q) k := rfl

end LeanCanny.Algebra.IntegralMixedFramedCutChoiceBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRootPullback
public import LeanCanny.Algebra.IntegralMixedFramedPrefixHeight
/-! # Original script bounds survive the complete-root projection -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRootPullback
open IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)

theorem familyInputs (P : Parameters) (D : Plan P) (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (L F C : List Bool → ℕ) (h : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) :
    IntegralMixedFramedStepHeight.FamilyInputs (parameters P project extra) (plan P D project extra)
      (L ∘ project) (F ∘ project) (C ∘ project) where
  script root := h.script (project root)
  default root := h.default (project root)

end LeanCanny.Algebra.IntegralMixedFramedRootPullback

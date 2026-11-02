/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutChoiceProfile
public import LeanCanny.Algebra.IntegralMixedFramedFullChoiceProbe
/-! # Full finite-choice coefficients preserve the literal old source profile -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

noncomputable def coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (choice k : ℕ) :=
  IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state key) ((family P D H).birth_bound key)
    ((family P D H).rule key) (IntegralMixedRelativeCuts.atChoice ((family P D H).rule key) ((family P D H).kind key) choice) k

theorem atProfile (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (choice k : ℕ) :
    HEq (coefficient P D H key choice k)
      ((IntegralMixedFramedCutSourceBits.atProfile P D
        (IntegralMixedFramedCutChoiceBits.profile P D (IntegralMixedFramedCutSourceBits.profile P D H key) choice)).coefficient [] k) := by
  rfl

private theorem coefficient_congr {S T : PaddedIntegralGeneratorSource.Source} (h : S=T) (k : ℕ) :
    HEq (S.coefficient [] k) (T.coefficient [] k) := by cases h; rfl

theorem pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (key : List Bool) (choice k : ℕ) :
    HEq (coefficient (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D H project extra) key choice k)
      (coefficient P D H (IntegralMixedFramedRootPullback.key project key) choice k) := by
  have HA:=atProfile (IntegralMixedFramedRootPullback.parameters P project extra)
    (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D H project extra) key choice k
  have HB:=atProfile P D H (IntegralMixedFramedRootPullback.key project key) choice k
  have HS:=IntegralMixedFramedCutRootPullback.atProfile P D project extra
    (IntegralMixedFramedCutChoiceBits.profile _ _ (IntegralMixedFramedCutSourceBits.profile _ _
      (IntegralMixedFramedRootPullback.data P D H project extra) key) choice)
  rw [IntegralMixedFramedCutChoiceBits.pullback_profile,IntegralMixedFramedCutRootPullback.profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

theorem planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) (choice k : ℕ) :
    HEq (coefficient (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key choice k)
      (coefficient P D H key choice k) := by
  have HA:=atProfile (IntegralMixedFramedNormalizationBits.planned P L F C)
    (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
    (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key choice k
  have HB:=atProfile P D H key choice k
  have HS:=IntegralMixedFramedCutPlanning.atProfile P D L F C
    (IntegralMixedFramedCutChoiceBits.profile _ _ (IntegralMixedFramedCutSourceBits.profile _ _
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key) choice)
  rw [IntegralMixedFramedCutChoiceBits.planned_profile,IntegralMixedFramedCutPlanning.profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

theorem clipped (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (choice bound k : ℕ)
    (hb : IntegralMixedRelativeCuts.choiceIndex ((family P D H).rule key) ((family P D H).kind key)≤bound) :
    coefficient P D H key (min choice bound) k=coefficient P D H key choice k := by
  unfold coefficient
  rw [IntegralMixedRelativeCuts.atChoice_clipped _ _ _ _ hb]

end LeanCanny.Algebra.IntegralMixedFramedChoiceCoefficientBits

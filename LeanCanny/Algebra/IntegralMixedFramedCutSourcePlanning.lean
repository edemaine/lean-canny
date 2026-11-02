/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutRootPullback
public import LeanCanny.Algebra.IntegralMixedFramedNormalizationPlanning
/-! # Budget planning preserves the entire untruncated relative factor -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutPlanning
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedNormalizationBits

noncomputable def profile (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (k : IntegralMixedFramedCutSourceBits.Profile (planned P L F C) (plannedPlan P D L F C)) :
    IntegralMixedFramedCutSourceBits.Profile P D := ⟨k.root,k.birth,k.bounded,k.selection⟩

theorem atProfile (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (k : IntegralMixedFramedCutSourceBits.Profile (planned P L F C) (plannedPlan P D L F C)) :
    IntegralMixedFramedCutSourceBits.atProfile (planned P L F C) (plannedPlan P D L F C) k=
      IntegralMixedFramedCutSourceBits.atProfile P D (profile P D L F C k) := by rfl

theorem selection (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.selection (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C) key=IntegralMixedFramedHistoryFamilyBits.selection P D H key := by
  have HI:=planned_instruction P D L F C key
  have HS : HEq (IntegralMixedFramedHistoryFamilyBits.instruction (planned P L F C) (plannedPlan P D L F C) key).source
      (IntegralMixedFramedHistoryFamilyBits.instruction P D key).source := heq_of_eq (congrArg (fun I=>I.source) HI)
  have HV:=IntegralMixedFramedCutRootPullback.selectAt_heq _ _ rfl rfl (heq_of_eq HI) HS (H.fallback key)
  apply eq_of_heq
  exact (heq_of_eq (IntegralMixedFramedRootPullback.selection_selectAt (planned P L F C)
    (plannedPlan P D L F C) (plannedData P D H L F C) key)).trans
    (HV.trans (heq_of_eq (IntegralMixedFramedRootPullback.selection_selectAt P D H key).symm))

theorem profile_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :
    profile P D L F C (IntegralMixedFramedCutSourceBits.profile (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C) key)=IntegralMixedFramedCutSourceBits.profile P D H key := by
  apply IntegralMixedFramedCutSourceBits.Profile.ext
  · rfl
  · rfl
  · exact heq_of_eq (selection P D H L F C key)

private theorem coefficient_congr {S T : PaddedIntegralGeneratorSource.Source} (h : S=T) (k : ℕ) :
    HEq (S.coefficient [] k) (T.coefficient [] k) := by cases h; rfl

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) (k : ℕ) :
    HEq ((IntegralMixedFramedCutSourceBits.source (planned P L F C) (plannedPlan P D L F C)
      (plannedData P D H L F C)).coefficient key k)
      ((IntegralMixedFramedCutSourceBits.source P D H).coefficient key k) := by
  have HA:=IntegralMixedFramedCutSourceBits.coefficient_atProfile (planned P L F C)
    (plannedPlan P D L F C) (plannedData P D H L F C) key k
  have HB:=IntegralMixedFramedCutSourceBits.coefficient_atProfile P D H key k
  have HS:=atProfile P D L F C (IntegralMixedFramedCutSourceBits.profile (planned P L F C)
    (plannedPlan P D L F C) (plannedData P D H L F C) key)
  rw [profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

end LeanCanny.Algebra.IntegralMixedFramedCutPlanning

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedAllCoordinateTransport
/-! # Actual coordinate-degree bounds survive root and budget transport -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinateBoundsBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedCutProbeTaskBits (parameters original)
open IntegralMixedFramedCutProbeTransportBits (lifted liftedPlan liftedData plan data)
open IntegralMixedFramedAllCoordinateTaskBits (query)

noncomputable def atProfile (P : Parameters) (D : Plan P) (q : IntegralMixedFramedCutSourceBits.Profile P D) : ℕ :=
  IntegralMixedCoordinateTrailing.ChoiceBound (IntegralMixedFramedRootPullback.instructionAt P D q.root q.birth).source q.selection.rule

theorem atProfile_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) q=
      atProfile P D (IntegralMixedFramedCutSourceBits.profile P D H (IntegralMixedVirtualTaskBits.saved P q)) := rfl

theorem atProfile_planned (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)) :
    atProfile (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) q=
      atProfile P D (IntegralMixedFramedCutPlanning.profile P D L F C q) := rfl

theorem atProfile_pullback (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)) :
    atProfile (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra) q=
      atProfile P D (IntegralMixedFramedCutRootPullback.profile P D project extra q) := rfl

attribute [local irreducible] atProfile

theorem planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) :
    atProfile (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedCutSourceBits.profile _ _ (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key)=
      atProfile P D (IntegralMixedFramedCutSourceBits.profile P D H key) := by
  rw [atProfile_planned]
  rw [IntegralMixedFramedCutPlanning.profile_key]

theorem pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (key : List Bool) :
    atProfile (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)
      (IntegralMixedFramedCutSourceBits.profile _ _ (IntegralMixedFramedRootPullback.data P D H project extra) key)=
      atProfile P D (IntegralMixedFramedCutSourceBits.profile P D H (IntegralMixedFramedRootPullback.key project key)) := by
  rw [atProfile_pullback]
  rw [IntegralMixedFramedCutRootPullback.profile_key]

theorem query_choiceBound (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (q : List Bool) (hc : IntegralMixedVirtualContextBits.context P (original q)) :
    IntegralMixedCoordinateCoefficientTasks.choiceBound (parameters P L F C)
      (family (parameters P L F C) (plan P D L F C) (data P D H L F C)) (query P L F C q)=
      IntegralMixedCoordinateCoefficientTasks.choiceBound P (family P D H) (original q) := by
  rw [atProfile_key]
  have HA:=planned (lifted P) (liftedPlan P D) (liftedData P D H) (L∘pairFst) (F∘pairFst) (C∘pairFst)
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
  have HB:=pullback P D H pairFst IntegralMixedFramedModulusPacket.extra
    (IntegralMixedVirtualTaskBits.saved (parameters P L F C) (query P L F C q))
  rw [IntegralMixedFramedAllCoordinateTaskBits.query_saved P L F C q hc] at HB
  exact HA.trans (HB.trans (atProfile_key P D H (original q)).symm)

theorem coordinate_cap (P : Parameters) (L F C : List Bool→ℕ) (q : List Bool)
    (hj : IntegralMixedFramedAllCoordinateTaskBits.coordinate P q≤P.ambient (RankedHistoryTask.root (original q))+1) :
    IntegralMixedFramedAllCoordinateTaskBits.coordinate P q≤numericCap (parameters P L F C) (IntegralMixedFramedCutProbeTaskBits.root q) := by
  apply hj.trans
  have HT : P.ambient (RankedHistoryTask.root (original q))+1=
      (parameters P L F C).ambient (IntegralMixedFramedCutProbeTaskBits.root q)+1 := by
    simp only [parameters,IntegralMixedFramedNormalizationBits.planned,IntegralMixedFramedRootPullback.parameters,
      IntegralMixedFramedCutProbeTaskBits.root,Function.comp_apply,pairFst_pair]
  rw [HT]
  exact (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinateBoundsBits

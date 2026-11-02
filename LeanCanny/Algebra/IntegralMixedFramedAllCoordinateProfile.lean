/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutChoiceProfile
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot

/-! # Unrestricted coordinate coefficients retain the actual old profile

The outer coordinate-Y degree and inner parameter-E degree are independent.
Changing Y degree does not clip it at a recorded trailing-factor choice and
does not change the script, selected rule, old bank or coefficient basis.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedAllCoordinateBits
open LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical

noncomputable def selection {n : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    (s : IntegralMixedFullHistoryFamilyBits.Selection P) (j c : ℕ) : IntegralMixedFullHistoryFamilyBits.Selection P :=
  {s with kind:=(IntegralMixedRelativeCuts.Kind.coordinate
    ⟨j%(n-s.rule.critical.offset.val+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
    ⟨c%IntegralMixedCoordinateTrailing.ChoiceBound P s.rule,Nat.mod_lt _ (Nat.succ_pos _)⟩)}

noncomputable def profile (P : Parameters) (D : Plan P) (q : IntegralMixedFramedCutSourceBits.Profile P D) (j c : ℕ) :
    IntegralMixedFramedCutSourceBits.Profile P D := {q with selection:=selection q.selection j c}

noncomputable def coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (j c k : ℕ) :=
  IntegralMixedCutMatrix.coefficientMatrix ((family P D H).state key) ((family P D H).birth_bound key)
    ((family P D H).rule key) (IntegralMixedCoordinateCoefficientSnapshot.kind (family P D H) key j c) k

theorem atProfile (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (j c k : ℕ) :
    HEq (coefficient P D H key j c k)
      ((IntegralMixedFramedCutSourceBits.atProfile P D
        (profile P D (IntegralMixedFramedCutSourceBits.profile P D H key) j c)).coefficient [] k) := by rfl

theorem pullback_profile (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)) (j c : ℕ) :
    IntegralMixedFramedCutRootPullback.profile P D project extra (profile _ _ q j c)=
      profile P D (IntegralMixedFramedCutRootPullback.profile P D project extra q) j c := rfl

theorem planned_profile (P : Parameters) (D : Plan P) (L F C : List Bool→ℕ)
    (q : IntegralMixedFramedCutSourceBits.Profile (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)) (j c : ℕ) :
    IntegralMixedFramedCutPlanning.profile P D L F C (profile _ _ q j c)=
      profile P D (IntegralMixedFramedCutPlanning.profile P D L F C q) j c := rfl

private theorem coefficient_congr {S T : PaddedIntegralGeneratorSource.Source} (h : S=T) (k : ℕ) :
    HEq (S.coefficient [] k) (T.coefficient [] k) := by cases h; rfl

theorem pullback (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (key : List Bool) (j c k : ℕ) :
    HEq (coefficient (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D H project extra) key j c k)
      (coefficient P D H (IntegralMixedFramedRootPullback.key project key) j c k) := by
  have HA:=atProfile (IntegralMixedFramedRootPullback.parameters P project extra)
    (IntegralMixedFramedRootPullback.plan P D project extra) (IntegralMixedFramedRootPullback.data P D H project extra) key j c k
  have HB:=atProfile P D H (IntegralMixedFramedRootPullback.key project key) j c k
  have HS:=IntegralMixedFramedCutRootPullback.atProfile P D project extra
    (profile _ _ (IntegralMixedFramedCutSourceBits.profile _ _ (IntegralMixedFramedRootPullback.data P D H project extra) key) j c)
  rw [pullback_profile,IntegralMixedFramedCutRootPullback.profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

theorem planned (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (key : List Bool) (j c k : ℕ) :
    HEq (coefficient (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key j c k)
      (coefficient P D H key j c k) := by
  have HA:=atProfile (IntegralMixedFramedNormalizationBits.planned P L F C)
    (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
    (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key j c k
  have HB:=atProfile P D H key j c k
  have HS:=IntegralMixedFramedCutPlanning.atProfile P D L F C
    (profile _ _ (IntegralMixedFramedCutSourceBits.profile _ _ (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key) j c)
  rw [planned_profile,IntegralMixedFramedCutPlanning.profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

end LeanCanny.Algebra.IntegralMixedFramedAllCoordinateBits

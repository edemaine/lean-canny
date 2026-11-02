/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCutSourceProfile
public import LeanCanny.Algebra.IntegralMixedFramedRootPullbackData
/-! # Honest root pullback preserves all four complete relative factors

The complete original selected rule, kind and old prefix are transported.
Enlarging only the modulus budget therefore retains every untruncated
coefficient matrix, including coefficients above the recorded scalar degree.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCutRootPullback
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedHistoryScript (Instruction)
open IntegralMixedFramedRootPullback (parameters plan data key selectAt transportSelection)
open scoped Classical

theorem selectAt_heq {n n' B B' : ℕ} (I : Instruction n B) (J : Instruction n' B')
    (hn : n=n') (hB : B=B') (hI : HEq I J) (hS : HEq I.source J.source)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection J.source) :
    HEq (selectAt I (transportSelection hn hS fallback)) (selectAt J fallback) := by
  cases hn
  cases hB
  have H : I=J:=eq_of_heq hI
  cases H
  rfl

theorem selection_heq (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) :
    HEq (IntegralMixedFramedHistoryFamilyBits.selection (parameters P project extra) (plan P D project extra)
      (data P D H project extra) q)
      (IntegralMixedFramedHistoryFamilyBits.selection P D H (key project q)) := by
  have HS:=selectAt_heq _ _ (congrArg P.ambient (IntegralMixedFramedRootPullback.key_root project q).symm)
    (congrArg P.width (IntegralMixedFramedRootPullback.key_root project q).symm)
    (IntegralMixedFramedRootPullback.instruction_heq P D project extra q)
    (IntegralMixedFramedRootPullback.instruction_source P D project extra q) (H.fallback (key project q))
  exact (heq_of_eq (IntegralMixedFramedRootPullback.selection_selectAt (parameters P project extra)
    (plan P D project extra) (data P D H project extra) q)).trans
    (HS.trans (heq_of_eq (IntegralMixedFramedRootPullback.selection_selectAt P D H (key project q)).symm))

noncomputable def profile (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (k : IntegralMixedFramedCutSourceBits.Profile (parameters P project extra) (plan P D project extra)) :
    IntegralMixedFramedCutSourceBits.Profile P D := ⟨project k.root,k.birth,k.bounded,k.selection⟩

theorem atProfile (P : Parameters) (D : Plan P) (project : List Bool→List Bool) (extra : List Bool→ℕ)
    (k : IntegralMixedFramedCutSourceBits.Profile (parameters P project extra) (plan P D project extra)) :
    IntegralMixedFramedCutSourceBits.atProfile (parameters P project extra) (plan P D project extra) k=
      IntegralMixedFramedCutSourceBits.atProfile P D (profile P D project extra k) := by rfl

theorem profile_key (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) :
    profile P D project extra (IntegralMixedFramedCutSourceBits.profile (parameters P project extra)
      (plan P D project extra) (data P D H project extra) q)=
        IntegralMixedFramedCutSourceBits.profile P D H (key project q) := by
  apply IntegralMixedFramedCutSourceBits.Profile.ext
  · exact (IntegralMixedFramedRootPullback.key_root project q).symm
  · exact (IntegralMixedFramedRootPullback.key_prefix P project extra q).symm
  · exact selection_heq P D H project extra q

private theorem coefficient_congr {S T : PaddedIntegralGeneratorSource.Source} (h : S=T) (k : ℕ) :
    HEq (S.coefficient [] k) (T.coefficient [] k) := by cases h; rfl

theorem coefficient (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool→List Bool) (extra : List Bool→ℕ) (q : List Bool) (k : ℕ) :
    HEq ((IntegralMixedFramedCutSourceBits.source (parameters P project extra) (plan P D project extra)
      (data P D H project extra)).coefficient q k)
      ((IntegralMixedFramedCutSourceBits.source P D H).coefficient (key project q) k) := by
  have HA:=IntegralMixedFramedCutSourceBits.coefficient_atProfile (parameters P project extra)
    (plan P D project extra) (data P D H project extra) q k
  have HB:=IntegralMixedFramedCutSourceBits.coefficient_atProfile P D H (key project q) k
  have HS:=atProfile P D project extra (IntegralMixedFramedCutSourceBits.profile (parameters P project extra)
    (plan P D project extra) (data P D H project extra) q)
  rw [profile_key] at HS
  exact HA.trans ((coefficient_congr HS k).trans HB.symm)

end LeanCanny.Algebra.IntegralMixedFramedCutRootPullback

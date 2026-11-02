/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionOriginalSpace
/-! # Literal creating leading integers and complete-root transport

These integers are the actual denominators introduced by scalar root steps.
They retain the same chronological source and prefix under context changes,
root pullback and automatic task-budget planning.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan prefixLength)
open IntegralMixedFramedHistoryScript
open IntegralMixedFramedCompanionQueryBits (callerModulus)
open scoped Classical

noncomputable def atPrefix (P : Parameters) (D : Plan P) (k : IntegralMixedFramedCompanionBits.PrefixKey P) : ℤ :=
  IntegralMixedFramedHistoryFamilyBits.creatorLeading P D k.root
    (paddedPast (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D k.root) (D.rules k.root) k.birth)
    ((chronological (D.rules k.root) k.birth).getD (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P D k.root))
    (by rw [paddedPast_length]; exact k.bounded)

theorem leading_atPrefix (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    IntegralMixedFramedCompanionBits.leading P D H key=atPrefix P D (IntegralMixedFramedCompanionBits.profile P key) := rfl

theorem leading_congr (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (x y : List Bool) (hr : pairFst x=pairFst y) (hb : prefixLength P x=prefixLength P y) :
    IntegralMixedFramedCompanionBits.leading P D H x=IntegralMixedFramedCompanionBits.leading P D H y := by
  rw [leading_atPrefix,leading_atPrefix]
  exact congrArg (atPrefix P D) (IntegralMixedFramedCompanionBits.PrefixKey.ext
    (IntegralMixedFramedCompanionBits.profile P x) (IntegralMixedFramedCompanionBits.profile P y) hr hb)

theorem pullback_atPrefix (P : Parameters) (D : Plan P) (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (k : IntegralMixedFramedCompanionBits.PrefixKey (IntegralMixedFramedRootPullback.parameters P project extra)) :
    atPrefix (IntegralMixedFramedRootPullback.parameters P project extra) (IntegralMixedFramedRootPullback.plan P D project extra) k=
      atPrefix P D (IntegralMixedFramedRootPullback.profile P project extra k) := rfl

theorem pullback_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (project : List Bool → List Bool) (extra : List Bool → ℕ)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra)) (key : List Bool) :
    IntegralMixedFramedCompanionBits.leading (IntegralMixedFramedRootPullback.parameters P project extra)
      (IntegralMixedFramedRootPullback.plan P D project extra) Hnew key=
      IntegralMixedFramedCompanionBits.leading P D H (IntegralMixedFramedRootPullback.key project key) := by
  rw [leading_atPrefix,leading_atPrefix,pullback_atPrefix,IntegralMixedFramedRootPullback.profile_key]

theorem planned_leading (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedCompanionBits.leading (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key=
      IntegralMixedFramedCompanionBits.leading P D H key := rfl

noncomputable def value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : List Bool :=
  residueBits (IntegralMixedFramedCompanionBits.leading P D H (PaddedIntegralGeneratorSource.base q) : ZMod (callerModulus q))

private theorem command_default {n B : ℕ} {I J : Instruction n B}
    (h : I=J) (hJ : J.command=IntegralMixedFullHistoryScript.defaultCommand) :
    I.command=IntegralMixedFullHistoryScript.defaultCommand := by cases h; exact hJ

theorem leading_default (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool)
    (hb : P.cap (pairFst key)≤prefixLength P key) : IntegralMixedFramedCompanionBits.leading P D H key=1 := by
  have HC := command_default (IntegralMixedFramedCompanionDefaultBits.instruction_default P D key hb) (by rfl)
  unfold IntegralMixedFramedCompanionBits.leading
  rw [HC]
  exact Polynomial.leadingCoeff_X

end LeanCanny.Algebra.IntegralMixedFramedLeadingBits

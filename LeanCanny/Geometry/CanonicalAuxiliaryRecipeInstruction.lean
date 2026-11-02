/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryRecordRule
/-! # Literal scheduled instructions for a finite list of original cut labels -/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.ETR IntegralMixedHistory
open IntegralMixedFramedHistoryScript (Instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B D : ℕ} {t : Term} {ht : (AuxiliaryTiltedTerm.term n t).degreeBound≤D}

noncomputable def recipeSource (G0 birth : ℕ) : SpatialSource (n+2) :=
  source birth D t ht birth B (nextHeight n S B D 1^birth*G0)

noncomputable def recipeInstruction
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 birth choice degree : ℕ) : Instruction (n+2) B :=
  IntegralMixedAuxiliaryLimitRecord.instruction (recipeSource (n:=n) (S:=S) (B:=B) (D:=D) (t:=t) (ht:=ht) G0 birth)
    birth 0 choice degree (by exact hcap)

theorem SampleFrame.record_instruction (F : SampleFrame n S B D t ht) (hF : F.Front)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source F.frozen D t ht F.birth B F.height) F.criticalRule))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) F.criticalRule) :
    IntegralMixedLimitCoordinate.instruction F.state F.criticalRule F.coordinate c d hd =
      IntegralMixedAuxiliaryLimitRecord.instruction (source F.frozen D t ht F.birth B F.height)
        F.frozen 0 c.val d (by exact hcap) := by
  have H:=F.record_command hF hcap c d hd
  unfold IntegralMixedLimitCoordinate.instruction IntegralMixedAuxiliaryLimitRecord.instruction
  congr 1
  simpa only [Nat.zero_add] using H.symm

theorem SampleFrame.instruction_eq_recipe (F : SampleFrame n S B D t ht) (hF : F.Front)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+3) (FixedLeadingTiltedSource.degree D)≤2^B)
    (G0 birth : ℕ) (hf : F.frozen=birth) (hb : F.birth=birth)
    (hG : F.height=nextHeight n S B D 1^birth*G0)
    (c : Fin (IntegralMixedLimitCoordinate.ChoiceBound (source F.frozen D t ht F.birth B F.height) F.criticalRule))
    (d : ℕ) (hd : d≤IntegralMixedLimitCoordinate.degree (source F.frozen D t ht F.birth B F.height) F.criticalRule) :
    IntegralMixedLimitCoordinate.instruction F.state F.criticalRule F.coordinate c d hd =
      recipeInstruction (S:=S) (t:=t) (ht:=ht) hcap G0 birth c.val d := by
  refine (F.record_instruction hF hcap c d hd).trans ?_
  generalize c.val=choice
  simp only [recipeInstruction,recipeSource,hf,hb,hG]
end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory

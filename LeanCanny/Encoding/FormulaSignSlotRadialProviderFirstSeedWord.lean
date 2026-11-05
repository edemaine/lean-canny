/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedTuple
public import LeanCanny.Encoding.IntegralFramedPhysicalExactVertex
/-! # A fresh own word for the complete provider seed tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedRunObservation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem planned_observation (P : Parameters) (D : Plan P)
    (L F C : List Bool→ℕ) (r : List Bool) :
    ofCommands (initial (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C) r) (D.rules r)
        (by change (D.rules r).length≤P.cap r+1+1;have H := D.room r;omega)=
      ofCommands (initial P D r) (D.rules r) (by have H := D.room r;omega) := rfl

private theorem prefix_count (B : IntegralFramedBankQuery.Bank) (c : List Bool) :
    prefixLength B.parameters (B.key c)=
      (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count :=
  (family_birth B.parameters B.plan B.data (B.key c)).symm

noncomputable def JointSampled (B : IntegralFramedBankQuery.Bank) (c : List Bool) (u : ℕ→ℝ) : Prop :=
  ∃w,∃hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w,
    w.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input B) c ∧
    ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val

private theorem sample_bank (BB : IntegralFramedBankQuery.Bank) (c r : List Bool)
    (hr : pairFst (BB.key c)=r) (hc : prefixLength BB.parameters (BB.key c)=(BB.plan.rules r).length)
    (u : ℕ→ℝ)
    (hu : (ofCommands (initial BB.parameters BB.plan r) (BB.plan.rules r)
      (by have H := BB.plan.room r;omega)).Roots u) : JointSampled BB c u :=
  IntegralFramedPhysicalSquare.exists_full_observation BB.parameters BB.plan BB.data
    BB.nodes BB.factor BB.seed BB.bounds BB.key BB.positive c r hr hc u hu

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderIntegerSource.source

local notation "RP" => FormulaSignSlotRadialProviderRecordPlan.parameters
local notation "RD" => FormulaSignSlotRadialProviderRecordPlan.plan
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def seedContext (c : List Bool) := pair (root c) []

theorem full_length (c : List Bool) : ((RD).rules (root c)).length=
    FormulaSignSlotRadialProviderRecordPlan.fullCount (root c) := by
  rw [full_commands,List.length_append,List.length_map,commands_count,older_length]
  exact Nat.add_comm _ _

theorem full_prefix (c : List Bool) : prefixLength P ((B).key (seedContext c))=((D).rules (root c)).length := by
  have H := FormulaSignSlotRadialProviderRecordPlan.bank_count (seedContext c)
  rw [seedContext,pairFst_pair] at H
  have HH := (prefix_count B (seedContext c)).trans H
  exact HH.trans (full_length c).symm

noncomputable def Sampled (c : List Bool) (u : ℕ→ℝ) := JointSampled B (seedContext c) u

theorem sampling_observation (c : List Bool) :
    ofCommands (initial P D (root c)) ((D).rules (root c))
      (by have H := (D).room (root c);omega)=observation c :=
  planned_observation RP RD (fun _=>3) FormulaSignSlotRadialProviderRecordPlan.factor
    FormulaSignSlotRadialProviderRecordPlan.seed (root c)

attribute [local irreducible] observation Sampled JointSampled

theorem sample_tuple (c : List Bool) (u : ℕ→ℝ) (hu : (observation c).Roots u) : Sampled c u := by
  have HZ := (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots u) (sampling_observation c)).mpr hu
  unfold Sampled
  exact sample_bank B (seedContext c) (root c)
    (by simp only [FormulaSignSlotRadialProviderRecordPlan.bank,
      FormulaSignSlotRadialProviderRecordPlan.bankKey,seedContext,keyAt,pairFst_pair])
    (full_prefix c) u HZ

end LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeed

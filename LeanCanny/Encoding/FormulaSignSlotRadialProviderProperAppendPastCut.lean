/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPastCritical
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCutStage
/-! # Actual general provider appends preserve every historical creating-cut receipt -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
local notation "O" => FormulaSignSlotRadialProviderRecordPrefix.observation
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "natural" => FormulaSignSlotRadialProviderRecordPrefix.natural
local notation "saved" => FormulaSignSlotRadialProviderRecordPrefix.cutSaved
local notation "receipt" => FormulaSignSlotRadialProviderRecordPrefix.ownCutReceipt

private theorem command_heq {a b u v : ℕ}
    (I : IntegralMixedFramedHistoryScript.Instruction a u) (J : IntegralMixedFramedHistoryScript.Instruction b v)
    (ha : a=b) (hb : u=v) (he : HEq I J) : HEq I.command J.command := by
  subst b
  subst v
  cases eq_of_heq he
  rfl

private theorem cut_instruction_saved (r : List Bool) (j : ℕ)
    (hj : j<IntegralMixedCausalRecordPlanBits.count r) :
    HEq (instruction P D (saved r (N r+j))) (IntegralMixedFramedRootPullback.instructionAt P D r (N r+j)) := by
  have HB : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    omega
  have HR : pairFst (saved r (N r+j))=r :=
    (congrArg pairFst (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq r _ HB)).trans (keyAt_root _ _ _)
  have HP : prefixLength P (saved r (N r+j))=N r+j :=
    (family_birth P D H _).symm.trans (FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth r _ HB)
  exact IntegralMixedFramedRootPullback.instructionAt_congr P D _ r _ _ HR HP

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRecordPrefix.observation FormulaSignSlotRadialProviderRecordPrefix.snapshot
  FormulaSignSlotRadialProviderAtomic.root FormulaSignSlotRadialProviderAtomic.dimension
  preparedRoot start parentCommands

theorem past_cut_receipt (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (leftCode rightCode : List Bool) (side : Bool) (hE : EndpointsGood old leftCode rightCode)
    (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input (C (preparedRoot old leftCode rightCode side)) w)
    (hr : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands old hv hd leftCode rightCode side hE),
      natural (preparedRoot old leftCode rightCode side) w hw r=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv r)
    (j : ℕ) (hj : j<start old) :
    receipt (preparedRoot old leftCode rightCode side) w hw j
      (hj.trans_le (prefix_fit old hv hd leftCode rightCode side hE)) ↔
    receipt (FormulaSignSlotRadialProviderAtomic.root old) (FormulaSignSlotRadialProviderAtomic.word old)
      (FormulaSignSlotRadialProviderAtomic.full_valid old hv) j (hj.trans_le (start_fit old hv)) := by
  let r := preparedRoot old leftCode rightCode side
  let l := FormulaSignSlotRadialProviderAtomic.root old
  let kr := saved r (N r+j)
  let kl := saved l (N l+j)
  have HC := prepared_provider old leftCode rightCode side
  have HCount := prepared_count old hv hd leftCode rightCode side hE
  have HN : N r=N l := FormulaSignSlotRadialProviderRecordPrefix.count_eq r l HC
  have HJL : j<IntegralMixedCausalRecordPlanBits.count l := hj.trans_le (start_fit old hv)
  have HJR : j<IntegralMixedCausalRecordPlanBits.count r := HJL.trans_eq HCount.symm
  have HI0 := FormulaSignSlotRadialProviderRecordPrefix.creating_heq r l HC HCount j
    (Nat.succ_le_of_lt HJR) (fun i hi=>prepared_record old hv leftCode rightCode side i (hi.trans_le (Nat.succ_le_of_lt hj)))
  have HI : HEq (instruction P D kr) (instruction P D kl) :=
    (cut_instruction_saved r j HJR).trans (HI0.trans (cut_instruction_saved l j HJL).symm)
  have HData : IntegralMixedPrefixSnapshot.ofState ((G).state kr)=IntegralMixedPrefixSnapshot.ofState ((G).state kl) :=
    (FormulaSignSlotRadialProviderRecordPrefix.cut_snapshot r j HJR).trans
      ((prefix_snapshot old hv hd leftCode rightCode side hE j hj.le).trans
        (FormulaSignSlotRadialProviderRecordPrefix.cut_snapshot l j HJL).symm)
  have HCmd : HEq (instruction P D kr).command (instruction P D kl).command := command_heq _ _
    (congrArg IntegralMixedPrefixSnapshot.Data.ambient HData) (congrArg IntegralMixedPrefixSnapshot.Data.width HData) HI
  let vr := (O r j HJR.le).point (natural r w hw)
  let vl := (O l j HJL.le).point (FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv)
  let ar := FormulaSignSlotRadialProviderAtomic.bankField (C r) w hw (N r+j)
  let al := FormulaSignSlotRadialProviderAtomic.field old hv (N l+j)
  have HValues : ∀i<(G).birth kr,vr i=vl i := by
    intro i hi
    have HB : N r+j<FormulaSignSlotRadialProviderRecordPlan.fullCount r := by
      unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
      omega
    have HBirth := FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth r (N r+j) HB
    have HI' : i<N l+j := hi.trans_eq (HBirth.trans (congrArg (·+j) HN))
    exact past_prefix_point old hv hd leftCode rightCode side hE _ _ (past_raw_native old hv hd leftCode rightCode side hE _ hr) j hj.le i HI'
  have HA : ar=al := by
    dsimp only [ar]
    rw [HN]
    exact past_fields old hv hd leftCode rightCode side hE w hw hr (N l+j) (by change N l+j<N l+start old;omega)
  have H0 := IntegralMixedPrefixSnapshot.familyCutReceipt_transport P D H kr kl HData HCmd vr vl ar HValues
  have H1 : IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl ar ↔
      IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl al :=
    Iff.of_eq (congrArg (IntegralMixedPrefixSnapshot.familyCutReceipt P D H kl vl) HA)
  exact H0.trans H1

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

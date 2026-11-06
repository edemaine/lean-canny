/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWordReceipt
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # The fresh retained word preserves every old natural column and field -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem count_full (B : IntegralFramedBankQuery.Bank) (c r : List Bool)
    (hr : pairFst (B.key c)=r) (hc : prefixLength B.parameters (B.key c)=(B.plan.rules r).length) :
    IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)=arity (B.plan.rules r) := by
  unfold IntegralFramedPhysicalSquare.count commands
  rw [hr,hc,paddedPast_full]

private theorem snapshot_birth (B : IntegralFramedBankQuery.Bank) (c : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count=
      (family B.parameters B.plan B.data).birth (B.key c) := rfl

private theorem observation_lists {n S B : ℕ} {Q : SpatialSource n}
    (x : State Q S B 0 (Fin 0)) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    IntegralMixedFramedRunObservation.ofCommands x cs hc=
      IntegralMixedFramedRunObservation.ofCommands x ds hd := by cases he;rfl

private theorem field_observation_generic (B : IntegralFramedBankQuery.Bank) (T : IntegralMixedHeaderTablesBits.Tables)
    (hT : IntegralMixedFramedHeaderBits.Represents B.parameters B.plan B.data T)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c w)
    (r : List Bool) (hr : pairFst (B.key c)=r)
    (hc : prefixLength B.parameters (B.key c)=(B.plan.rules r).length)
    (u : ℕ→ℝ) (HJ : ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
      IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
        B.key B.positive c w hw i=u i.val)
    (b : ℕ) (hb : b<(IntegralMixedFramedBankSnapshotBits.atKey B.parameters B.plan B.data (B.key c)).count) :
    IntegralFramedPhysicalBankTerm.env B T hT c w hw b=
      (IntegralMixedFramedRunObservation.ofCommands (initial B.parameters B.plan r) (B.plan.rules r)
        (by have H := B.plan.room r;omega)).point u
          ((family B.parameters B.plan B.data).birth (B.key c)-1-b) := by
  have HB : b<(family B.parameters B.plan B.data).birth (B.key c) := hb
  rw [IntegralFramedPhysicalBankTerm.env_chronological B T hT c w hw b hb]
  have HP := IntegralFramedPhysicalSquare.point_of_joint_natural B.parameters B.plan B.data
    B.nodes B.factor B.seed B.bounds B.key B.positive c w hw u HJ
    ⟨(family B.parameters B.plan B.data).birth (B.key c)-1-b,by have H := B.positive c;omega⟩
  refine HP.trans ?_
  apply congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point u _)
  cases hr
  apply observation_lists
  unfold commands
  rw [hc,paddedPast_full]

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor levelProgram
  IntegralMixedFramedHistoryFamilyBits.family

theorem parent_arity_le_local (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    arity (parentCommands old hv hd e he)≤arity (levelProgram old hv hd e he R false) := by
  unfold levelProgram
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem local_arity_le_full (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he) :
    arity (levelProgram old hv hd e he R false)≤arity ((D).rules (preparedRoot old e)) := by
  rw [full_commands old hv hd e he R]
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem sampled_arity (old : List Bool) (e : ℕ) :
    IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)))=
      arity ((D).rules (preparedRoot old e)) :=
  count_full B _ (preparedRoot old e)
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old e))
    ((FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old e)).trans
      (full_rules_length (preparedRoot old e)).symm)

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {e : ℕ} {he : e<endBirth (dimension old) (N old) old}
  {p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ}

theorem WordReceipt.old_raw (W : WordReceipt old hv hd e he p)
    (i : ℕ) (hi : i<arity (parentCommands old hv hd e he)) : W.tuple i=oldNatural old hv i := by
  have HL := W.local_readback.2.2 ((enumerate (parentCommands old hv hd e he)).symm ⟨i,hi⟩)
  unfold parentTuple at HL
  simp only [Equiv.apply_symm_apply,Fin.val_mk] at HL
  exact (W.full.2.1 i (hi.trans_le (parent_arity_le_local old hv hd e he W.pair))).trans HL

theorem WordReceipt.natural_eq (W : WordReceipt old hv hd e he p) (i : ℕ)
    (hi : i<arity ((D).rules (preparedRoot old e))) :
    FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old e) W.word W.valid i=W.tuple i := by
  have HC : i<IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e))) :=
    hi.trans_eq (sampled_arity old e).symm
  unfold FormulaSignSlotRadialProviderRecordPrefix.natural FormulaSignSlotRadialProviderRecordPrefix.bankNatural
    IntegralFramedPhysicalPrefixObservation.tuple IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HC]
  exact W.joint ⟨i,HC⟩

theorem WordReceipt.old_raw_native (W : WordReceipt old hv hd e he p)
    (i : ℕ) (hi : i<arity (parentCommands old hv hd e he)) :
    FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old e) W.word W.valid i=oldNatural old hv i :=
  (W.natural_eq i (hi.trans_le ((parent_arity_le_local old hv hd e he W.pair).trans
    (local_arity_le_full old hv hd e he W.pair)))).trans (W.old_raw i hi)

theorem WordReceipt.field_observation (W : WordReceipt old hv hd e he p)
    (b : ℕ) (hb : b<fullBirth old e) :
    FormulaSignSlotRadialProviderAtomic.bankField
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)) W.word W.valid b=
      (fullObservation old e).point W.tuple (fullBirth old e-1-b) := by
  have HC : b<(IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)))).count := by
    have HE := (snapshot_birth B (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e))).trans
      ((family_birth _ _ _ _).trans (FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old e)))
    exact hb.trans_eq HE.symm
  have HP := FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old e)
  have HL : prefixLength (B).parameters ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)))=
      ((B).plan.rules (preparedRoot old e)).length := HP.trans (full_rules_length _).symm
  have H := field_observation_generic B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents _ W.word W.valid (preparedRoot old e)
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old e)) HL W.tuple W.joint b HC
  have HB : (family (B).parameters (B).plan (B).data).birth ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)))=fullBirth old e :=
    (family_birth _ _ _ _).trans HP
  rw [HB] at H
  unfold fullObservation
  change IntegralFramedPhysicalBankTerm.env B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents _ W.word W.valid b=
      (IntegralMixedFramedRunObservation.ofCommands
        (initial (B).parameters (B).plan (preparedRoot old e)) ((B).plan.rules (preparedRoot old e))
        (by have HR := (B).plan.room (preparedRoot old e);omega)).point W.tuple (fullBirth old e-1-b)
  exact H

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend

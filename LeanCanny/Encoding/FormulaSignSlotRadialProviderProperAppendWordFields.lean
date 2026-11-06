/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordReceipt
public import LeanCanny.Encoding.IntegralFramedPhysicalBankChronologicalPoint
/-! # The fresh proper word preserves exact raw columns and all chronological field readbacks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
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
section Bounds
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
  (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
local notation "r" => preparedRoot old R.leftSpec R.rightSpec side
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  preparedRoot parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues
  IntegralMixedFramedHistoryFamilyBits.family

theorem parent_arity_le_canonical : arity cs≤(canonicalObservation old hv hd left right R side).arity := by
  change arity cs≤arity (canonicalCompiledProgram old hv hd left right R side)
  unfold canonicalCompiledProgram
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem local_arity_le_full : arity (compiledProgram old hv hd left right R side)≤arity ((D).rules r) := by
  rw [full_commands old hv hd left right R side]
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem canonical_arity_le_full : (canonicalObservation old hv hd left right R side).arity≤arity ((D).rules r) := by
  have HA : arity (compiledProgram old hv hd left right R side)=
      (canonicalObservation old hv hd left right R side).arity := by
    simpa only [compiledObservation,IntegralMixedFramedRunObservation.ofCommands] using
      tuple_arity old hv hd left right R side
  exact HA.symm.le.trans (local_arity_le_full old hv hd left right R side)

theorem sampled_arity : IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key
    (FormulaSignSlotRadialProviderRecordPrefix.context r))=arity ((D).rules r) :=
  count_full B _ r (FormulaSignSlotRadialProviderRecordPrefix.key_root r)
    ((FormulaSignSlotRadialProviderRecordPrefix.full_prefix r).trans (full_rules_length r).symm)

end Bounds

variable {old : List Bool} {hv : FormulaSignSlotRadialProviderAtomic.Valid old}
  {hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {z : ℕ→ℝ} {p0 : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ}
local notation "e" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd e he
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  preparedRoot parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentCommands
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentValues
  IntegralMixedFramedHistoryFamilyBits.family

theorem WordReceipt.natural_eq (W : WordReceipt old hv hd left right R side z p0) (i : ℕ)
    (hi : i<arity ((D).rules (preparedRoot old R.leftSpec R.rightSpec side))) :
    FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old R.leftSpec R.rightSpec side) W.word W.valid i=W.tuple i := by
  have HC : i<IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side))) :=
    hi.trans_eq (sampled_arity old hv hd left right R side).symm
  unfold FormulaSignSlotRadialProviderRecordPrefix.natural FormulaSignSlotRadialProviderRecordPrefix.bankNatural
    IntegralFramedPhysicalPrefixObservation.tuple IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HC]
  exact W.joint ⟨i,HC⟩


theorem WordReceipt.field_observation (W : WordReceipt old hv hd left right R side z p0)
    (b : ℕ) (hb : b<fullBirth old hv hd left right R side) :
    FormulaSignSlotRadialProviderAtomic.bankField
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side)) W.word W.valid b=
      (fullObservation old hv hd left right R side).point W.tuple (fullBirth old hv hd left right R side-1-b) := by
  have HC : b<(IntegralMixedFramedBankSnapshotBits.atKey (B).parameters (B).plan (B).data ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side)))).count := by
    have HE := (snapshot_birth B (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side))).trans
      ((family_birth _ _ _ _).trans (FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old R.leftSpec R.rightSpec side)))
    exact hb.trans_eq HE.symm
  have HP := FormulaSignSlotRadialProviderRecordPrefix.full_prefix (preparedRoot old R.leftSpec R.rightSpec side)
  have HL : prefixLength (B).parameters ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side)))=
      ((B).plan.rules (preparedRoot old R.leftSpec R.rightSpec side)).length := HP.trans (full_rules_length _).symm
  have H := field_observation_generic B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents _ W.word W.valid (preparedRoot old R.leftSpec R.rightSpec side)
    (FormulaSignSlotRadialProviderRecordPrefix.key_root (preparedRoot old R.leftSpec R.rightSpec side)) HL W.tuple W.joint b HC
  have HB : (family (B).parameters (B).plan (B).data).birth ((B).key
      (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old R.leftSpec R.rightSpec side)))=fullBirth old hv hd left right R side :=
    (family_birth _ _ _ _).trans HP
  change (family (B).parameters (B).plan (B).data).birth
    ((B).key (pair (preparedRoot old R.leftSpec R.rightSpec side) []))=_ at HB
  rw [HB] at H
  unfold fullObservation
  change IntegralFramedPhysicalBankTerm.env B FormulaSignSlotRadialProviderRecordPlan.tables
    FormulaSignSlotRadialProviderAtomic.bank_represents _ W.word W.valid b=
      (IntegralMixedFramedRunObservation.ofCommands
        (initial (B).parameters (B).plan (preparedRoot old R.leftSpec R.rightSpec side)) ((B).plan.rules (preparedRoot old R.leftSpec R.rightSpec side))
        (by have HR := (B).plan.room (preparedRoot old R.leftSpec R.rightSpec side);omega)).point W.tuple (fullBirth old hv hd left right R side-1-b)
  exact H

theorem WordReceipt.old_raw_native (W : WordReceipt old hv hd left right R side z p0)
    (hOld : ∀j,j<arity cs→z j=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv j)
    (i : ℕ) (hi : i<arity (parentCommands old hv hd R.leftSpec R.rightSpec side
      (endpoints_good old hv hd left right R))) :
    FormulaSignSlotRadialProviderRecordPrefix.natural (preparedRoot old R.leftSpec R.rightSpec side)
      W.word W.valid i=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv i := by
  have HC : i<arity cs := hi.trans_eq
    (parent_layout old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R)).2.1
  have HL := HC.trans_le (parent_arity_le_canonical old hv hd left right R side)
  exact (W.natural_eq i (HL.trans_le (canonical_arity_le_full old hv hd left right R side))).trans
    ((W.preserved i HL).trans (hOld i HC))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend

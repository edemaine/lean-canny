/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRowMeaning
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperCriticalPreparedPrefix
/-! # An accepted provider word realizes both literal probe parent states -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem realizes_from_snapshot {n S W m : ℕ} {Q : SpatialSource n} {ι : Type}
    (x : State Q S W m ι) (d : IntegralMixedPrefixSnapshot.Data)
    (he : IntegralMixedPrefixSnapshot.ofState x=d) (v : ℕ→ℝ) (hv : d.Realizes v) :
    IntegralMixedIntegerRealization.Realizes x v :=by
  exact (congrArg (fun a : IntegralMixedPrefixSnapshot.Data=>a.Realizes v) he).mpr hv

local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "C"=>IntegralMixedCausalRecordPlanBits.count
local notation "N"=>FormulaSignSlotRadialProviderRecordPlan.count
local notation "snap"=>FormulaSignSlotRadialProviderRecordPrefix.snapshot
local notation "obs"=>FormulaSignSlotRadialProviderRecordPrefix.observation
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryScript.run IntegralMixedHistory.reframe

noncomputable def probeStart (z : List Bool):=IntegralMixedRoadmapBadProbePacket.count (oldPacket z)-1

theorem probe_old_records (z : List Bool) :
    IntegralMixedCausalRecordPlanBits.records (FormulaSignSlotRadialProviderAtomic.root (atomic z))=
      IntegralMixedRoadmapBadProbePacket.raw (oldPacket z) :=
  FormulaSignSlotRadialProviderProperCritical.base_records (atomic z)

theorem probe_old_count (z : List Bool) : C (FormulaSignSlotRadialProviderAtomic.root (atomic z))=
    IntegralMixedRoadmapBadProbePacket.count (oldPacket z) :=
  FormulaSignSlotRadialProviderProperCritical.base_count (atomic z)

theorem probe_start_fit (z : List Bool) : probeStart z≤C (FormulaSignSlotRadialProviderAtomic.root (atomic z)) :=by
  rw [probe_old_count]
  exact Nat.sub_le _ _

noncomputable def probeValues (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :=
  (obs (FormulaSignSlotRadialProviderAtomic.root (atomic z)) (probeStart z) (probe_start_fit z)).point
    (FormulaSignSlotRadialProviderRecordPrefix.natural (FormulaSignSlotRadialProviderAtomic.root (atomic z))
      (FormulaSignSlotRadialProviderAtomic.word (atomic z)) (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv))

theorem probe_snapshot_original (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (parentKey mean z))=
      snap (FormulaSignSlotRadialProviderAtomic.root (atomic z)) (probeStart z) (probe_start_fit z) :=by
  have HC:=row_count_positive z hv
  have HP:=(root_provider mean z).trans (FormulaSignSlotRadialProviderAtomic.root_provider (atomic z)).symm
  have HCount : C (root mean z)=C (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=
    (root_count mean z HC).trans (probe_old_count z).symm
  have HCodes : ∀i,i<probeStart z→IntegralMixedCausalRecordPlanBits.code (root mean z) i=
      IntegralMixedCausalRecordPlanBits.code (FormulaSignSlotRadialProviderAtomic.root (atomic z)) i:=by
    intro i hi
    unfold IntegralMixedCausalRecordPlanBits.code
    rw [probe_old_records]
    have HE:=raw_older mean z i hi
    simpa only [IntegralMixedCausalRecordPlanBits.records,root,pairFst_pair,pairSnd_pair] using HE
  have HE:=FormulaSignSlotRadialProviderRecordPrefix.snapshot_eq (root mean z)
    (FormulaSignSlotRadialProviderAtomic.root (atomic z)) HP HCount (probeStart z)
    ((probe_start_fit z).trans_eq HCount.symm) HCodes
  exact (parent_snapshot mean z HC).trans HE

theorem probe_parent_realizes (mean : Bool) (z : List Bool)
    (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    IntegralMixedIntegerRealization.Realizes ((G).state (parentKey mean z)) (probeValues z hv) :=by
  have HO:=FormulaSignSlotRadialProviderRecordPrefix.snapshot_word_realizes
    (FormulaSignSlotRadialProviderAtomic.root (atomic z)) (FormulaSignSlotRadialProviderAtomic.word (atomic z))
    (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) (probeStart z) (probe_start_fit z)
  exact realizes_from_snapshot _ _ (probe_snapshot_original mean z hv) _ HO

theorem probe_parent_count (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z)) :
    N (FormulaSignSlotRadialProviderAtomic.root (atomic z))+probeStart z=creating z :=by
  have HC:=row_count_positive z hv
  unfold probeStart creating IntegralMixedRoadmapBadProbePacket.creating initial FormulaSignSlotRadialProviderAtomic.initial
  omega

theorem probeValues_field (z : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid (atomic z))
    (i : ℕ) (hi : i<creating z) :
    probeValues z hv i=originalValue (atomic z) hv (creating z-1-i) :=by
  have HB:=probe_parent_count z hv
  have HF:=FormulaSignSlotRadialProviderRecordPrefix.word_value
    (FormulaSignSlotRadialProviderAtomic.root (atomic z)) (FormulaSignSlotRadialProviderAtomic.word (atomic z))
    (FormulaSignSlotRadialProviderAtomic.full_valid (atomic z) hv) (probeStart z) (probe_start_fit z) i
    (hi.trans_eq HB.symm)
  have HVal : probeValues z hv i=FormulaSignSlotRadialProviderAtomic.field (atomic z) hv
      (N (FormulaSignSlotRadialProviderAtomic.root (atomic z))+probeStart z-1-i):=by
    simpa only [probeValues,FormulaSignSlotRadialProviderAtomic.field,
      FormulaSignSlotRadialProviderAtomic.context,FormulaSignSlotRadialProviderRecordPrefix.context] using HF
  have HE:=congrArg (fun m : ℕ=>m-1-i) HB
  have HBound : N (FormulaSignSlotRadialProviderAtomic.root (atomic z))+probeStart z≤
      FormulaSignSlotRadialProviderRecordPlan.fullCount (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=by
    unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
    have HS:=probe_start_fit z
    omega
  have HL : creating z-1-i<FormulaSignSlotRadialProviderRecordPlan.fullCount
      (FormulaSignSlotRadialProviderAtomic.root (atomic z)):=by omega
  exact HVal.trans ((congrArg (FormulaSignSlotRadialProviderAtomic.field (atomic z) hv) HE).trans
    (originalValue_field (atomic z) hv (creating z-1-i) HL).symm)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow

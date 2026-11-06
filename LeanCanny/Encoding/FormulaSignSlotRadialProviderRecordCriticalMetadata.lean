/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFirstSeedMetadata
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrefixMetadata
public import LeanCanny.Geometry.IntegralMixedChronologicalMidpointCriticalReadback
/-! # Literal provider point codes determine their native critical metadata -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalMetadata
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open FormulaSignSlotRadialProviderFirstSeed (stageHeader later_header)
open FormulaSignSlotRadialProviderRecordPrefix (context)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem frame_header {n B birth : ℕ} (Q : SpatialSource n) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (labels : List Bool) (g j : ℕ) (HG : IntegralMixedChronologicalFrameCode.PointGood n birth labels g j) :
    let H := (IntegralMixedCausalUnitRecordBits.record Q hn birth
      (IntegralMixedChronologicalFrameCode.code n labels g j) hcap).template.header
    H.context=1 ∧ H.offset+H.coordinate=j := by
  have HC := IntegralMixedChronologicalFrameCode.raw_command Q hn labels g j HG hcap 1 one_ne_zero
  have HH := congrArg IntegralMixedCommandHeaderBits.command HC
  change (IntegralMixedCausalUnitRecordBits.record Q hn birth
    (IntegralMixedChronologicalFrameCode.code n labels g j) hcap).template.header=_ at HH
  dsimp only
  rw [HH]
  exact ⟨rfl,IntegralMixedChronologicalFrame.raw_selected birth labels g j HG⟩

private theorem midpoint_header {n B birth : ℕ} (Q : SpatialSource n) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) Q.degree≤2^B)
    (labels : List Bool) (a b g j : ℕ) (HG : IntegralMixedChronologicalMidpointCode.Good n birth labels a b g j) :
    let H := (IntegralMixedCausalUnitRecordBits.record Q hn birth
      (IntegralMixedChronologicalMidpointCode.code n labels a b g j) hcap).template.header
    H.context=1 ∧ H.offset+H.coordinate=j := by
  have HC := IntegralMixedChronologicalMidpointCode.raw_command Q hn labels a b g j HG hcap 1 one_ne_zero
  have HH := congrArg IntegralMixedCommandHeaderBits.command HC
  change (IntegralMixedCausalUnitRecordBits.record Q hn birth
    (IntegralMixedChronologicalMidpointCode.code n labels a b g j) hcap).template.header=_ at HH
  dsimp only
  rw [HH]
  exact ⟨rfl,IntegralMixedChronologicalMidpoint.raw_selected birth labels a b g j HG⟩

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source

theorem native_header (r : List Bool) (b : ℕ) :
    FormulaSignSlotRadialProviderRecordPrefix.header r b=stageHeader r b :=
  FormulaSignSlotRadialProviderRecordPrefix.header_actual r b

private theorem stage_packet (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardScan.stage (pair c (List.replicate b true))=b := by
  rw [IntegralFramedPhysicalCriticalGuardScan.stage,pairSnd_pair,List.length_replicate]
private theorem datum_packet (f : List Bool→List Bool) (c : List Bool) (b : ℕ) :
    IntegralFramedPhysicalCriticalGuardTest.keyDatum f (pair c (List.replicate b true))=f c :=
  congrArg f (pairFst_pair _ _)

theorem active_of_header (r : List Bool) (b : ℕ)
    (hb : b<FormulaSignSlotRadialProviderRecordPlan.fullCount r) (hc : (stageHeader r b).context=1) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) b := by
  constructor
  · rw [datum_packet,stage_packet]
    change b<prefixLength P ((B).key (context r))
    exact hb.trans_eq (FormulaSignSlotRadialProviderRecordPrefix.full_prefix r).symm
  · change (FormulaSignSlotRadialProviderRecordPrefix.header r b).context=1
    rw [native_header]
    exact hc

theorem selected_of_header (r : List Bool) (b j : ℕ)
    (hs : (stageHeader r b).offset+(stageHeader r b).coordinate=j) :
    FormulaSignSlotRadialProviderAtomic.selected (context r) b=j := by
  change (FormulaSignSlotRadialProviderRecordPrefix.header r b).offset+
    (FormulaSignSlotRadialProviderRecordPrefix.header r b).coordinate=j
  rw [native_header]
  exact hs

theorem frame_metadata (r : List Bool) (i : ℕ) (hi : i<IntegralMixedCausalRecordPlanBits.count r)
    (labels : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalFrameCode.PointGood ((P).ambient r) (N r+i) labels g j)
    (hc : IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedChronologicalFrameCode.code ((P).ambient r) labels g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) (N r+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) (N r+i)=j := by
  have HH : (stageHeader r (N r+i)).context=1 ∧
      (stageHeader r (N r+i)).offset+(stageHeader r (N r+i)).coordinate=j := by
    rw [later_header r i hi,hc]
    exact frame_header _ _ _ labels g j hg
  exact ⟨active_of_header r _ (by change N r+i<N r+_;omega) HH.1,selected_of_header r _ j HH.2⟩

theorem midpoint_metadata (r : List Bool) (i : ℕ) (hi : i<IntegralMixedCausalRecordPlanBits.count r)
    (labels : List Bool) (a b g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good ((P).ambient r) (N r+i) labels a b g j)
    (hc : IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedChronologicalMidpointCode.code ((P).ambient r) labels a b g j) :
    FormulaSignSlotRadialProviderAtomic.Active (context r) (N r+i) ∧
      FormulaSignSlotRadialProviderAtomic.selected (context r) (N r+i)=j := by
  have HH : (stageHeader r (N r+i)).context=1 ∧
      (stageHeader r (N r+i)).offset+(stageHeader r (N r+i)).coordinate=j := by
    rw [later_header r i hi,hc]
    exact midpoint_header _ _ _ labels a b g j hg
  exact ⟨active_of_header r _ (by change N r+i<N r+_;omega) HH.1,selected_of_header r _ j HH.2⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordCriticalMetadata

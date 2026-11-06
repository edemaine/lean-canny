/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeProvenance
public import LeanCanny.Encoding.IntegralMixedReservedCutModuloInstruction
/-! # Checked provider bad hints emit the actual ordinary current-Q cut -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeCommand
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits IntegralMixedCausalRecordBits
open IntegralMixedRoadmapBadProbePacket (root count labels field prefixCodes probe)
open FormulaSignSlotRadialProviderBadProbeProvenance (prepared saved)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.source
local notation "dim" => FormulaSignSlotRadialProviderBadProbeTest.dimension
local notation "ini" => FormulaSignSlotRadialProviderBadProbeTest.initial
local notation "wid" => FormulaSignSlotRadialProviderBadProbeTest.width

private theorem view_currentQ (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool) :
    commonDenominator (IntegralMixedFramedFamilyRunView.stateView p d h key)=
      commonDenominator ((family p d h).state key) := rfl

private theorem rule_Q_congr {n b : ℕ} (d : IntegralMixedCutRecordConstructor.Data n b)
    (u v : ℤ) (hu : u≠0) (hv : v≠0) (he : u=v) : d.rule u hu=d.rule v hv := by
  cases he
  rfl

private theorem ordinary_cut {n B : ℕ} (I : IntegralMixedFramedHistoryScript.Instruction n B)
    (h : IntegralMixedReservedCutModuloInstruction.OrdinaryInstruction I) :
    IntegralFramedCreatingCut.IsCut I.command := by
  cases I with
  | mk src hc command =>
    cases command with
    | integer => exact False.elim h
    | critical => exact False.elim h
    | cut => trivial

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source

noncomputable def appendPlan : Plan P := IntegralMixedSourceIntegerRecordAppend.plan P (fun r _=>Q r)
  FormulaSignSlotRadialProviderRecordPlan.positive (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
  FormulaSignSlotRadialProviderRecordPlan.spatial_cap N T FormulaSignSlotRadialProviderRecordPlan.source_nonzero
  FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room

theorem append_plan_eq : appendPlan=D := rfl
noncomputable abbrev appendData : IntegralMixedFramedHistoryFamilyBits.Data P appendPlan := H

private theorem package_eq :
    (⟨appendPlan,appendData⟩ : (d : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P d)=⟨D,H⟩ := rfl

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedFramedHistoryFamilyBits.family

variable (z : List Bool) (hh : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z)
local notation "d" => FormulaSignSlotRadialProviderBadProbeProvenance.data z hh
local notation "tag" => IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z))
local notation "choice" => Nat.fromBitsLE (field 2 z)
local notation "degree" => Nat.fromBitsLE (field 3 z)

noncomputable def creatingInstruction := IntegralMixedReservedCutModuloInstruction.born P (fun r _=>Q r)
  FormulaSignSlotRadialProviderRecordPlan.positive (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
  FormulaSignSlotRadialProviderRecordPlan.spatial_cap N T FormulaSignSlotRadialProviderRecordPlan.source_nonzero
  FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
  appendData (saved z) (prefixCodes (pairFst z)) d tag choice degree

theorem instruction_eq : instruction P D (saved z)=creatingInstruction z hh := by
  have HV := IntegralMixedReservedCutModuloInstruction.instruction_eq P (fun r _=>Q r)
    FormulaSignSlotRadialProviderRecordPlan.positive (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap N T FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    appendData (saved z) (prefixCodes (pairFst z)) d tag choice degree
    (FormulaSignSlotRadialProviderBadProbeProvenance.records_saved z hh)
    (FormulaSignSlotRadialProviderBadProbeProvenance.saved_prefix z hh)
  have HE := congrArg (fun a : Plan P=>instruction P a (saved z)) append_plan_eq
  exact HE.symm.trans HV

theorem currentQ : commonDenominator (IntegralMixedFramedFamilyRunView.stateView P appendPlan appendData (saved z))=
    commonDenominator ((G).state (saved z)) :=
  congrArg (fun dh : (a : Plan P)×IntegralMixedFramedHistoryFamilyBits.Data P a=>
    commonDenominator (IntegralMixedFramedFamilyRunView.stateView P dh.1 dh.2 (saved z))) package_eq |>.trans
      (view_currentQ P D H (saved z))

include hh in
theorem ordinary_instruction : IntegralMixedReservedCutModuloInstruction.OrdinaryInstruction (instruction P D (saved z)) := by
  rw [instruction_eq z hh]
  exact IntegralMixedReservedCutModuloInstruction.born_ordinary P (fun r _=>Q r)
    FormulaSignSlotRadialProviderRecordPlan.positive (fun r _=>FormulaSignSlotRadialProviderRecordPlan.spatial_degree r)
    FormulaSignSlotRadialProviderRecordPlan.spatial_cap N T FormulaSignSlotRadialProviderRecordPlan.source_nonzero
    FormulaSignSlotRadialProviderRecordPlan.source_degree_cap FormulaSignSlotRadialProviderRecordPlan.room
    appendData (saved z) (prefixCodes (pairFst z)) d tag choice degree (by
      rw [IntegralMixedChronologicalCutCode.ordinaryTag_index _ (IntegralMixedRoadmapBadProbeShape.tag_le _ _ _ z hh)]
      exact hh.2.2.1)

include hh in
theorem ordinary : IntegralMixedSelectedBadMembership.Ordinary ((G).rule (saved z)) ((G).kind (saved z)) :=
  IntegralMixedReservedCutModuloInstruction.selected_ordinary P D H (saved z) (ordinary_instruction z hh)

include hh in
theorem is_cut : IntegralFramedCreatingCut.IsCut (instruction P D (saved z)).command :=
  ordinary_cut _ (ordinary_instruction z hh)

include hh in
theorem interval_parent_cut : IntegralFramedCreatingCut.ParentCut P D
    (FormulaSignSlotRadialProviderCutInterval.parent (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)) := by
  unfold IntegralFramedCreatingCut.ParentCut
  rw [FormulaSignSlotRadialProviderBadProbeProvenance.context_saved z]
  exact is_cut z hh

attribute [local semireducible] IntegralMixedFramedHistoryFamilyBits.family

include hh in
theorem rule_eq : (G).rule (saved z)=(d).rule (commonDenominator ((G).state (saved z)))
    (commonDenominator_ne_zero ((G).state (saved z))) := by
  have HR : IntegralMixedReservedCutModuloInstruction.ruling (instruction P D (saved z))=
      some ((d).rule (commonDenominator (IntegralMixedFramedFamilyRunView.stateView P appendPlan appendData (saved z)))
        (commonDenominator_ne_zero (IntegralMixedFramedFamilyRunView.stateView P appendPlan appendData (saved z)))) := by
    rw [instruction_eq z hh]
    rfl
  exact (IntegralMixedReservedCutModuloInstruction.selected_rule P D H (saved z) _ HR).trans
    (rule_Q_congr d _ _ _ _ (currentQ z))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeCommand

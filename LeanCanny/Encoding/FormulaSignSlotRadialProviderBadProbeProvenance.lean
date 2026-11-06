/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeParent
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalContext
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeShape
/-! # A checked provider bad hint has its literal last creating prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeProvenance
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket (root count labels field prefixCodes probe creating)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "H" => FormulaSignSlotRadialProviderRecordPlan.certifiedData
local notation "G" => family P D H
local notation "N" => FormulaSignSlotRadialProviderRecordPlan.count
local notation "dim" => FormulaSignSlotRadialProviderBadProbeTest.dimension
local notation "ini" => FormulaSignSlotRadialProviderBadProbeTest.initial
local notation "wid" => FormulaSignSlotRadialProviderBadProbeTest.width

noncomputable def prepared (z : List Bool) := IntegralMixedRoadmapBadProbePacket.preparedRoot (dim z) z
noncomputable def birth (z : List Bool) := creating (ini z) (pairFst z)
noncomputable def saved (z : List Bool) := FormulaSignSlotRadialProviderRecordPrefix.cutSaved (prepared z) (birth z)

theorem provider (z : List Bool) : FormulaSignSlotRadialProviderRecordPlan.providerContext (prepared z)=
    FormulaSignSlotRadialProviderRecordPlan.providerContext (root (pairFst z)) :=
  FormulaSignSlotRadialProviderBadProbePrefix.prepared_provider (dim z) z

theorem prepared_dimension (z : List Bool) : (P).ambient (prepared z)=dim z :=
  FormulaSignSlotRadialProviderRecordPrefix.ambient _ _ (provider z)

theorem prepared_width (z : List Bool) : (P).width (prepared z)=wid z :=
  FormulaSignSlotRadialProviderRecordPrefix.width _ _ (provider z)

theorem initial_eq (z : List Bool) : ini z=N (root (pairFst z)) :=
  FormulaSignSlotRadialProviderBadProbeFields.initial_eq (pairFst z)

theorem prepared_initial (z : List Bool) : N (prepared z)=ini z :=
  (FormulaSignSlotRadialProviderBadProbePrefix.prepared_initial (dim z) z).trans (initial_eq z).symm

theorem prepared_source (z : List Bool) :
    HEq (FormulaSignSlotRadialProviderRecordPlan.spatial (prepared z))
      (FormulaSignSlotRadialProviderRecordPlan.spatial (root (pairFst z))) :=
  FormulaSignSlotRadialProviderRecordPrefix.source_heq _ _ (provider z)

theorem records (z : List Bool) : IntegralMixedCausalRecordPlanBits.records (prepared z)=
    WordList.encode (prefixCodes (pairFst z)++[probe (dim z) z]) := by
  simp only [prepared,IntegralMixedCausalRecordPlanBits.records,IntegralMixedRoadmapBadProbePacket.preparedRoot,
    IntegralMixedRoadmapBadProbePacket.preparedRaw,pairSnd_pair,pairFst_pair]

private theorem snapshot_index (r : List Bool) (i j : ℕ)
    (hi : i≤IntegralMixedCausalRecordPlanBits.count r) (hj : j≤IntegralMixedCausalRecordPlanBits.count r)
    (he : i=j) : FormulaSignSlotRadialProviderRecordPrefix.snapshot r i hi=
      FormulaSignSlotRadialProviderRecordPrefix.snapshot r j hj := by
  cases he
  rfl

private theorem family_ambient (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (key : List Bool) :
    (family p d h).ambient key=p.ambient (pairFst key) := rfl

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.source FormulaSignSlotRadialProviderRecordPlan.spatial
  FormulaSignSlotRadialProviderIntegerSource.source IntegralMixedFramedHistoryFamilyBits.family

variable (z : List Bool) (hh : IntegralMixedRoadmapBadProbePacket.HintGood (dim z) (ini z) (wid z) z)

include hh in
theorem prepared_count : IntegralMixedCausalRecordPlanBits.count (prepared z)=count (pairFst z) :=
  IntegralMixedRoadmapBadProbePacket.prepared_count (dim z) z hh.1

include hh in
theorem birth_eq : birth z=N (prepared z)+(count (pairFst z)-1) := by
  rw [prepared_initial]
  unfold birth creating
  have HC := hh.1
  omega

include hh in
theorem last_birth : birth z+1=FormulaSignSlotRadialProviderRecordPlan.fullCount (prepared z) := by
  unfold FormulaSignSlotRadialProviderRecordPlan.fullCount
  rw [prepared_count z hh,birth_eq z hh]
  have HC := hh.1
  omega

include hh in
theorem birth_fit : birth z<FormulaSignSlotRadialProviderRecordPlan.fullCount (prepared z) := by
  rw [←last_birth z hh]
  omega

include hh in
theorem saved_key : saved z=keyAt (prepared z) (birth z) (BinaryNatCode.encode 2) :=
  FormulaSignSlotRadialProviderRecordPrefix.cutSaved_eq _ _ (birth_fit z hh)

include hh in
theorem saved_root : pairFst (saved z)=prepared z :=
  (congrArg pairFst (saved_key z hh)).trans (keyAt_root _ _ _)

include hh in
theorem saved_birth : (G).birth (saved z)=birth z :=
  FormulaSignSlotRadialProviderRecordPrefix.cutSaved_birth _ _ (birth_fit z hh)

include hh in
theorem saved_prefix : prefixLength P (saved z)=N (pairFst (saved z))+(prefixCodes (pairFst z)).length := by
  have H0 := (family_birth P D H (saved z)).symm.trans (saved_birth z hh)
  rw [H0,saved_root z hh,prepared_initial]
  simp only [prefixCodes,List.length_map,List.length_range]
  unfold birth creating
  have HC := hh.1
  omega

include hh in
theorem saved_dimension : (P).ambient (pairFst (saved z))=dim z := by
  rw [saved_root z hh]
  exact prepared_dimension z

include hh in
theorem saved_width : (P).width (pairFst (saved z))=wid z := by
  rw [saved_root z hh]
  exact prepared_width z

include hh in
theorem creating_saved : birth z=N (pairFst (saved z))+(prefixCodes (pairFst z)).length := by
  rw [saved_root z hh,prepared_initial]
  simp only [prefixCodes,List.length_map,List.length_range]
  unfold birth creating
  have HC := hh.1
  omega

include hh in
theorem good_saved : IntegralMixedChronologicalCutCode.Good ((P).ambient (pairFst (saved z)))
    (N (pairFst (saved z))+(prefixCodes (pairFst z)).length) (labels (pairFst z))
    (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)) := by
  rw [saved_dimension z hh,←creating_saved z hh]
  exact IntegralMixedRoadmapBadProbeShape.raw_good (dim z) (ini z) (wid z) z hh

noncomputable def data := IntegralMixedChronologicalCutCode.rawData ((P).ambient (pairFst (saved z)))
  (N (pairFst (saved z))+(prefixCodes (pairFst z)).length) (labels (pairFst z))
  (WordListRecords.count (labels (pairFst z))+1) (Nat.fromBitsLE (field 1 z)) (good_saved z hh)

include hh in
theorem data_code : (data z hh).code
    (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
    (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))=probe (dim z) z := by
  rw [data,IntegralMixedChronologicalCutCode.rawData_code _ _ _ _ _ (good_saved z hh) _ _ _
    (IntegralMixedRoadmapBadProbeShape.tag_le _ _ _ z hh),saved_dimension z hh]
  rfl

include hh in
theorem records_saved : IntegralMixedCausalRecordPlanBits.records (pairFst (saved z))=
    WordList.encode (prefixCodes (pairFst z)++[(data z hh).code
      (IntegralMixedChronologicalCutCode.ordinaryTag (Nat.fromBitsLE (field 0 z)))
      (Nat.fromBitsLE (field 2 z)) (Nat.fromBitsLE (field 3 z))]) := by
  have HL := congrArg IntegralMixedCausalRecordPlanBits.records (saved_root z hh)
  have HR := congrArg (fun w=>WordList.encode (prefixCodes (pairFst z)++[w])) (data_code z hh).symm
  exact HL.trans ((records z).trans HR)

include hh in
theorem snapshot_saved : IntegralMixedPrefixSnapshot.ofState ((G).state (saved z))=
    FormulaSignSlotRadialProviderBadProbeParent.snapshot (prepared z) := by
  have HC : count (pairFst z)-1<IntegralMixedCausalRecordPlanBits.count (prepared z) := by
    rw [prepared_count z hh]
    have HP := hh.1
    omega
  have HS := FormulaSignSlotRadialProviderRecordPrefix.cut_snapshot (prepared z) _ HC
  have HL := congrArg (fun b=>IntegralMixedPrefixSnapshot.ofState ((G).state
    (FormulaSignSlotRadialProviderRecordPrefix.cutSaved (prepared z) b))) (birth_eq z hh)
  have HR := snapshot_index (prepared z) (count (pairFst z)-1)
    (IntegralMixedCausalRecordPlanBits.count (prepared z)-1) HC.le (Nat.sub_le _ _)
    (congrArg (fun n=>n-1) (prepared_count z hh).symm)
  exact HL.trans (HS.trans HR)



private theorem ready_family (F : IntegralMixedCutSource.Family) (key labels : List Bool)
    (hg : IntegralMixedChronologicalFrameCode.Good (F.ambient key) (F.birth key) labels)
    (hf : WordListRecords.count labels+1<F.ambient key+1) :
    (IntegralMixedPrefixSnapshot.ofState (F.state key)).Ready labels := ⟨F.birth_bound key,hg,hf⟩

include hh in
theorem snapshot_ready : (FormulaSignSlotRadialProviderBadProbeParent.snapshot (prepared z)).Ready (labels (pairFst z)) := by
  have HA : (G).ambient (saved z)=dim z := (family_ambient P D H (saved z)).trans (saved_dimension z hh)
  have HB := saved_birth z hh
  have HG : IntegralMixedChronologicalFrameCode.Good ((G).ambient (saved z)) ((G).birth (saved z))
      (labels (pairFst z)) :=
    Eq.mp (congrArg₂ (fun n b=>IntegralMixedChronologicalFrameCode.Good n b (labels (pairFst z))) HA.symm HB.symm) hh.2.1
  have HF : WordListRecords.count (labels (pairFst z))+1<(G).ambient (saved z)+1 := by
    rw [HA]
    exact lt_of_le_of_lt hh.2.2.2.1 hh.2.2.2.2.1
  exact (congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>d.Ready (labels (pairFst z)))
    (snapshot_saved z hh)).mp (ready_family G (saved z) _ HG HF)

theorem context_root : pairFst (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)=prepared z :=
  pairFst_pair _ _

theorem context_birth :
    (FormulaSignSlotRadialProviderCutInterval.birthWord
      (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)).length=birth z := by
  simp only [FormulaSignSlotRadialProviderBadProbeTest.intervalContext,IntegralMixedRoadmapBadProbePacket.intervalContext,
    FormulaSignSlotRadialProviderCutInterval.birthWord,pairSnd_pair,pairFst_pair,List.length_replicate]
  rfl

theorem context_parent : FormulaSignSlotRadialProviderCutInterval.parent
    (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)=
      FormulaSignSlotRadialProviderRecordPrefix.cutParent (prepared z) (birth z) := by
  have HE : pair (pairFst (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z))
      (pair (FormulaSignSlotRadialProviderCutInterval.birthWord
        (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)) [])=
      pair (prepared z) (pair (List.replicate (birth z) true) []) := by
    simp only [FormulaSignSlotRadialProviderBadProbeTest.intervalContext,IntegralMixedRoadmapBadProbePacket.intervalContext,
      FormulaSignSlotRadialProviderCutInterval.birthWord,pairSnd_pair,pairFst_pair]
    rfl
  exact (congrArg (IntegralFramedTraceCutTask.task P) HE).trans
    (FormulaSignSlotRadialProviderRecordPrefix.cutParent_eq (prepared z) (birth z)).symm

theorem context_saved : IntegralMixedVirtualTaskBits.saved P
    (FormulaSignSlotRadialProviderCutInterval.parent (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z))=saved z :=
  congrArg (IntegralMixedVirtualTaskBits.saved P) (context_parent z)

include hh in
theorem context_active : IntegralMixedFramedFullCutProbeBits.Active P
    (FormulaSignSlotRadialProviderCutInterval.parent (FormulaSignSlotRadialProviderBadProbeTest.intervalContext z)) := by
  rw [context_parent]
  exact FormulaSignSlotRadialProviderRecordPrefix.cut_active _ _ (birth_fit z hh)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderBadProbeProvenance

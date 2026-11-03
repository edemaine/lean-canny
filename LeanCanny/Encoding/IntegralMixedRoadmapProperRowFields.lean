/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSnapshot
/-! # Accepted chronological row coordinates survive the native header cap -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem ambient_numericCap (P : Parameters) (r : List Bool) :
    P.ambient r+1≤numericCap P r :=(IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank dimension initial creating

theorem parent_coordinate (mean : Bool) (z : List Bool)
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    get P Field.slot13 (parent hn ht ha hR0 mean z)=relativeCoordinate z :=by
  apply IntegralMixedRoutineContextQuery.query_coordinate
  rw [base,RankedHistoryTask.root_pack]
  have HB:=ambient_numericCap P (root hn ht ha hR0 mean z)
  rw [root_dimension hn ht ha hR0 mean z] at HB
  exact (Nat.sub_le (coordinate z) (offset z)).trans ((Nat.le_of_lt hg.1.2.2.2.2).trans HB)

theorem parent_context (mean : Bool) (z : List Bool) :
    get P Field.slot15 (parent hn ht ha hR0 mean z)=2 :=by
  apply IntegralMixedRoutineContextQuery.query_context
  rw [base,RankedHistoryTask.root_pack]
  have HB:=ambient_numericCap P (root hn ht ha hR0 mean z)
  rw [root_dimension hn ht ha hR0 mean z] at HB
  have HD : 3≤dimension hn ht ha hR0 z:=by
    rw [dimension,IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0]
    omega
  omega

theorem offset_count (z : List Bool) :offset z=WordListRecords.count (labels z)+1 :=by
  unfold offset labels
  rw [IntegralMixedRoadmapProper.labels_count]

private theorem ordinary_offset {a b : ℕ} (w : List Bool) (g j : ℕ)
    (hg : IntegralMixedChronologicalCutCode.Good a b w g j) :
    (IntegralMixedChronologicalCutCode.rawData a b w g j hg).critical.offset.val=WordListRecords.count w+1 :=by
  unfold IntegralMixedChronologicalCutCode.rawData
  change (LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame.pointData _ _ _ _ _ _).offset.val=_
  rw [LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame.pointData_offset,
    IntegralMixedChronologicalFrameCode.descriptor_length]

private theorem mean_offset {a b : ℕ} (w : List Bool) (left right g j : ℕ)
    (hg : IntegralMixedChronologicalMidpointCode.Good a b w left right g j) :
    (IntegralMixedChronologicalMeanCutCode.rawData a b w left right g j hg).critical.offset.val=
      WordListRecords.count w+1 :=by
  unfold IntegralMixedChronologicalMeanCutCode.rawData
  rw [LeanCanny.Geometry.IntegralMixedChronologicalMeanCut.data_offset,
    IntegralMixedChronologicalFrameCode.descriptor_length]

theorem parentData_offset (mean : Bool) (z : List Bool) (hg : ParentGood hn ht ha hR0 mean z) :
    (parentData hn ht ha hR0 mean z hg).critical.offset.val=offset z :=by
  rw [offset_count]
  cases mean
  · simp only [parentData,Bool.false_eq_true,ite_false]
    exact ordinary_offset _ _ _ hg.1
  · simp only [parentData,ite_true]
    exact mean_offset _ _ _ _ _ hg.2

local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P
  (IntegralFramedBankQuery.Bank.plan BK) (IntegralFramedBankQuery.Bank.data BK)

theorem rule_offset (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    ((G).rule (parentKey hn ht ha hR0 mean z)).critical.offset.val=offset z :=by
  rw [rule_at_parent hn ht ha hR0 mean z (row_count_positive hn ht ha hR0 z hv) hg]
  exact parentData_offset hn ht ha hR0 mean z _

theorem selected_coordinate (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (hg : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    (IntegralMixedCoordinateCoefficientSnapshot.coordinate G (parentKey hn ht ha hR0 mean z)
      (get P Field.slot13 (parent hn ht ha hR0 mean z))).val=relativeCoordinate z :=by
  change get P Field.slot13 (parent hn ht ha hR0 mean z)%_=relativeCoordinate z
  rw [parent_coordinate hn ht ha hR0 mean z hg]
  apply Nat.mod_eq_of_lt
  have HO:=rule_offset hn ht ha hR0 mean z hv hg
  have HD : (G).ambient (parentKey hn ht ha hR0 mean z)=dimension hn ht ha hR0 z:=
    parentDimension_eq hn ht ha hR0 mean z
  rw [HO,HD]
  have HJ:=hg.1.2.2.2.2
  have HF:=hg.1.2.2.2.1
  rw [←offset_count] at HF
  unfold relativeCoordinate
  omega

theorem parentKey_aux (mean : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    parentKey hn ht ha hR0 mean z=IntegralMixedFramedHistoryFamilyBits.keyAt
      (root hn ht ha hR0 mean z) (creating hn ht ha hR0 z) (BinaryNatCode.encode 2) :=by
  rw [parentKey_eq hn ht ha hR0 mean z (row_count_positive hn ht ha hR0 z hv),parent_context]

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

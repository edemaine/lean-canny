/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperProbeWords
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSelected
/-! # Metadata of the two actual reserved coordinate probes -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "BP"=>IntegralFramedBankQuery.Bank.plan BK
local notation "BH"=>IntegralFramedBankQuery.Bank.data BK
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P BP BH
attribute [local irreducible] creating parent terminal

theorem probe_parent_birth (mode : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    (G).birth (parentKey hn ht ha hR0 mode z)=creating hn ht ha hR0 z :=
  (IntegralMixedFramedHistoryFamilyBits.family_birth P BP BH _).trans
    (parentKey_prefix hn ht ha hR0 mode z (row_count_positive hn ht ha hR0 z hv))

theorem probe_terminal_count (mode : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    count hn ht ha hR0 mode z=creating hn ht ha hR0 z+1 :=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  unfold count terminal
  change (IntegralMixedFramedBankSnapshotBits.atKey
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha (radius_binary hR0))
    (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context hn ht ha hR0 mode z))).count=_
  rw [IntegralMixedAuxiliaryMarkedRecordPlan.bank_count]
  rw [context,pairFst_pair,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  rw [root_number hn ht ha hR0,root_count hn ht ha hR0 mode z HC]
  unfold creating IntegralMixedRoadmapBadProbePacket.creating
  omega

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

theorem probe_core (mode : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z) :
    IntegralMixedFramedCoordinateCoefficientSpaceBits.Core P (parent hn ht ha hR0 mode) z :=by
  have HC:=row_count_positive hn ht ha hR0 z hv
  have HD:=parent_coordinate hn ht ha hR0 mode z HR
  have HA : (P).ambient (RankedHistoryTask.root (parent hn ht ha hR0 mode z))=dimension hn ht ha hR0 z:=by
    rw [parent_root,root_dimension]
  have HV : birth P (parent hn ht ha hR0 mode z)<(P).cap (RankedHistoryTask.root (parent hn ht ha hR0 mode z)):=by
    rw [parent_birth hn ht ha hR0 mode z HC,parent_root]
    unfold IntegralMixedPhysicalMarkedPlan.bank
    change creating hn ht ha hR0 z<IntegralMixedAuxiliaryMarkedIntegerSource.number n (root hn ht ha hR0 mode z)+8+
      IntegralMixedCausalRecordPlanBits.count (root hn ht ha hR0 mode z)+2
    rw [root_number hn ht ha hR0,root_count hn ht ha hR0 mode z HC]
    unfold creating IntegralMixedRoadmapBadProbePacket.creating
    omega
  refine ⟨⟨HV,?_⟩,?_⟩
  · change 2≤get P .slot15 (parent hn ht ha hR0 mode z) ∧get P .slot15 (parent hn ht ha hR0 mode z)≤4
    rw [parent_context]
    exact ⟨by omega,by omega⟩
  · rw [HD,HA]
    exact (Nat.sub_le _ _).trans (Nat.le_of_lt HR.1.2.2.2.2)

theorem probe_metadata (mode : Bool) (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z))
    (HR : IntegralMixedRoadmapProperRowWitness.RowGood hn ht ha hR0 z)
    (c s : ℕ) (hc : c<creating hn ht ha hR0 z) (hs : s<creating hn ht ha hR0 z) :
    IntegralFramedPhysicalNear.Metadata P BP BH (parent hn ht ha hR0 mode) (terminal hn ht ha hR0 mode)
      (fun z=>count hn ht ha hR0 mode z-1-c) (fun z=>count hn ht ha hR0 mode z-1-s) z :=by
  have HT:=probe_terminal_count hn ht ha hR0 mode z hv
  refine ⟨probe_core hn ht ha hR0 mode z hv HR,?_,?_,?_,?_⟩
  · change (G).birth (parentKey hn ht ha hR0 mode z)≤count hn ht ha hR0 mode z
    rw [probe_parent_birth hn ht ha hR0 mode z hv,HT]
    omega
  · rw [terminal,Function.comp_apply,context]
    change pairFst ((BK).key (pair (root hn ht ha hR0 mode z) []))=pairFst (parentKey hn ht ha hR0 mode z)
    rw [IntegralMixedPhysicalMarkedPlan.key_root, parentKey_root]
  · change count hn ht ha hR0 mode z-1-c<count hn ht ha hR0 mode z
    omega
  · change count hn ht ha hR0 mode z-1-s<count hn ht ha hR0 mode z
    omega

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

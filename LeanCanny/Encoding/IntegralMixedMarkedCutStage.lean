/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshotFamily
public import LeanCanny.Encoding.IntegralMixedPhysicalCutRoot
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutScan
/-! # Every meaningful chronological cut uses its actual prefix algebra -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedCutStage
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H

noncomputable def parent (root :List Bool) (b :ℕ):=
  IntegralFramedPhysicalTraceCutSource.parent B (IntegralMixedPhysicalMarkedTest.sampleContext root) (List.replicate b true)
noncomputable def saved (root :List Bool) (b :ℕ):=IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR0 root b)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem parent_eq (root :List Bool) (b :ℕ):parent hn ht ha hR0 root b=
    IntegralFramedTraceCutTask.task P (pair root (pair (List.replicate b true) [])):=by
  simp only [parent,IntegralFramedPhysicalTraceCutSource.parent,IntegralMixedPhysicalMarkedTest.sampleContext,pairFst_pair]

theorem stage_bound (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root):b≤birthCap P root:=by
  have HC :(P).cap root=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root+2:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank;rfl
  change b≤(P).cap root+1
  rw [HC]
  omega

theorem saved_eq (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    saved hn ht ha hR0 root b=keyAt root b (BinaryNatCode.encode 2):=by
  unfold saved
  rw [parent_eq hn ht ha hR0 root b]
  have HB :IntegralFramedTraceCutTask.stage (pair root (pair (List.replicate b true) []))≤
      birthCap P (pairFst (pair root (pair (List.replicate b true) []))):=by
    simpa only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair,List.length_replicate] using
      stage_bound hn ht ha hR0 root b hb
  simpa only [pairFst_pair,IntegralFramedTraceCutTask.stage_packet,List.length_replicate] using
    IntegralFramedTraceCutTask.task_saved P (pair root (pair (List.replicate b true) [])) HB

theorem parent_birth (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :birth P (parent hn ht ha hR0 root b)=b:=by
  rw [parent_eq hn ht ha hR0 root b]
  have HB :IntegralFramedTraceCutTask.stage (pair root (pair (List.replicate b true) []))≤
      birthCap P (pairFst (pair root (pair (List.replicate b true) []))):=by
    simpa only [IntegralFramedTraceCutTask.stage_packet,pairFst_pair,List.length_replicate] using
      stage_bound hn ht ha hR0 root b hb
  simpa only [IntegralFramedTraceCutTask.stage_packet,List.length_replicate] using
    IntegralFramedTraceCutTask.task_birth P (pair root (pair (List.replicate b true) [])) HB

theorem saved_birth (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :(G).birth (saved hn ht ha hR0 root b)=b:=by
  exact ((IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth (parent hn ht ha hR0 root b)).trans
    (parent_birth hn ht ha hR0 root b hb)

attribute [local semireducible] IntegralMixedPhysicalMarkedPlan.bank

theorem snapshot_eq (root :List Bool) (j :ℕ) (hj :j<IntegralMixedCausalRecordPlanBits.count root) :
    IntegralMixedPrefixSnapshot.ofState ((G).state (saved hn ht ha hR0 root (number n root+8+j)))=
      IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 root j hj.le:=by
  have HB :number n root+8+j<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount;omega
  have HH:=congrArg (fun key=>IntegralMixedPrefixSnapshot.ofState ((G).state key))
    (saved_eq hn ht ha hR0 root _ HB)
  exact HH.trans (IntegralMixedMarkedPrefixSnapshot.family_keyAt hn ht ha hR0 root j hj.le (BinaryNatCode.encode 2))

theorem cut_active (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root)
    :
    IntegralMixedFramedFullCutProbeBits.Active P (parent hn ht ha hR0 root b):=by
  constructor
  · change birth P (parent hn ht ha hR0 root b)<(P).cap (RankedHistoryTask.root (parent hn ht ha hR0 root b))
    rw [parent_birth hn ht ha hR0 root b hb]
    have HR :RankedHistoryTask.root (parent hn ht ha hR0 root b)=root:=by
      rw [parent_eq,IntegralFramedTraceCutTask.task_root,pairFst_pair]
    rw [HR]
    have HC :(P).cap root=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root+2:=by
      unfold IntegralMixedPhysicalMarkedPlan.bank;rfl
    rw [HC]
    omega
  · have HE:=IntegralFramedTraceCutTask.task_context P (pair root (pair (List.replicate b true) []))
    rw [←parent_eq hn ht ha hR0 root b] at HE
    change 2≤get P .slot15 (parent hn ht ha hR0 root b) ∧get P .slot15 (parent hn ht ha hR0 root b)≤4
    rw [HE];decide

end LeanCanny.Encoding.IntegralMixedMarkedCutStage

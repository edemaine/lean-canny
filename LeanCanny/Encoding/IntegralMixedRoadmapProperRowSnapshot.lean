/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowRuling
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshotFamily

/-! # Ordinary and mean probes retain one literal older coefficient algebra

This compares whole prefix snapshots, including their sources, widths,
horizons and scalar algebras. It does not copy either complete word or
assert equality of independently chosen interpreting homs.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family keyAt)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters BK
local notation "D"=>IntegralFramedBankQuery.Bank.plan BK
local notation "H"=>IntegralFramedBankQuery.Bank.data BK
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank parentKey dimension initial creating

theorem row_root_reserved (mean : Bool) (z : List Bool) :root hn ht ha hR0 mean z=
    IntegralMixedMarkedPrefixRun.reservedRoot (IntegralMixedRoadmapAtomic.candidate (atomic z))
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)) (code hn ht ha hR0 mean z) [] :=rfl

theorem parentKey_eq (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    parentKey hn ht ha hR0 mean z=keyAt (root hn ht ha hR0 mean z) (creating hn ht ha hR0 z)
      (BinaryNatCode.encode (get P Field.slot15 (parent hn ht ha hR0 mean z))) :=by
  unfold parentKey IntegralMixedVirtualTaskBits.saved
  rw [parent_root,parent_birth hn ht ha hR0 mean z hc]

private def FamilySnapshot (K : IntegralFramedBankQuery.Bank) : Prop :=∀root j,
  ∀hj : j≤IntegralMixedCausalRecordPlanBits.count root,∀aux,
    IntegralMixedPrefixSnapshot.ofState ((family K.parameters K.plan K.data).state
      (keyAt root (number n root+8+j) aux))=
      IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 root j hj

private theorem family_snapshot : FamilySnapshot hn ht ha hR0 (n:=n) BK :=by
  have HB : BK=IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0):=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    rfl
  have HS : FamilySnapshot hn ht ha hR0 (n:=n)
      (IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0)):=by
    intro root j hj aux
    exact IntegralMixedMarkedPrefixSnapshot.family_keyAt hn ht ha hR0 root j hj aux
  exact (congrArg (fun K=>FamilySnapshot hn ht ha hR0 (n:=n) K) HB).mpr HS

noncomputable def parentSnapshot (mean : Bool) (z : List Bool):=
  IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 (root hn ht ha hR0 mean z)
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length
    (by rw [row_root_reserved,IntegralMixedMarkedPrefixRun.reserved_count];omega)

attribute [local irreducible] IntegralMixedMarkedPrefixSnapshot.snapshot

theorem parent_snapshot (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey hn ht ha hR0 mean z))=
      parentSnapshot hn ht ha hR0 mean z :=by
  have HS:=family_snapshot hn ht ha hR0 (root hn ht ha hR0 mean z)
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length
    (by rw [row_root_reserved,IntegralMixedMarkedPrefixRun.reserved_count];omega)
    (BinaryNatCode.encode (get P Field.slot15 (parent hn ht ha hR0 mean z)))
  have HB : number n (root hn ht ha hR0 mean z)+8+
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length=creating hn ht ha hR0 z:=by
    simpa only [parentBirth,parentKey_root] using parentBirth_eq hn ht ha hR0 mean z hc
  rw [HB,←parentKey_eq hn ht ha hR0 mean z hc] at HS
  exact HS

theorem parentSnapshot_eq (z : List Bool) :parentSnapshot hn ht ha hR0 false z=
    parentSnapshot hn ht ha hR0 true z :=by
  unfold parentSnapshot
  simp only [row_root_reserved]
  exact IntegralMixedMarkedPrefixSnapshot.reserved_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (atomic z)) (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z))
    (code hn ht ha hR0 false z) (code hn ht ha hR0 true z) [] []

theorem parent_state_snapshot_eq (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey hn ht ha hR0 false z))=
      IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey hn ht ha hR0 true z)) :=
  (parent_snapshot hn ht ha hR0 false z hc).trans
    ((parentSnapshot_eq hn ht ha hR0 z).trans (parent_snapshot hn ht ha hR0 true z hc).symm)

theorem parent_canonical (mean : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (oldPacket z)) :
    IntegralMixedHistory.Canonical ((family P D H).state (parentKey hn ht ha hR0 mean z)) :=by
  have HC : IntegralMixedHistory.Canonical (parentSnapshot hn ht ha hR0 mean z).state:=
    IntegralMixedMarkedPrefixSnapshot.canonical hn ht ha hR0 (root hn ht ha hR0 mean z)
      (IntegralMixedRoadmapBadProbePacket.prefixCodes (oldPacket z)).length _
  exact (congrArg (fun d : IntegralMixedPrefixSnapshot.Data=>IntegralMixedHistory.Canonical d.state)
    (parent_snapshot hn ht ha hR0 mean z hc)).mpr HC

theorem parent_state_snapshot_eq_valid (z : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic z)) :
    IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey hn ht ha hR0 false z))=
      IntegralMixedPrefixSnapshot.ofState ((family P D H).state (parentKey hn ht ha hR0 true z)) :=
  parent_state_snapshot_eq hn ht ha hR0 z (row_count_positive hn ht ha hR0 z hv)

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

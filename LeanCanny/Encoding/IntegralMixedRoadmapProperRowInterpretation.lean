/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperRowSnapshot
public import LeanCanny.Encoding.IntegralMixedRoadmapProperFieldReadback
public import LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
/-! # Accepted row guards give one common older interpreting hom

The words retain their own roots. All older quotient readbacks agree by
actual field scans; the hom is constructed from the ordinary full word.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "rr"=>IntegralMixedRoadmapProperRow.root hn ht ha hR0
local notation "rc"=>IntegralMixedRoadmapProperRow.context hn ht ha hR0
local notation "rb"=>IntegralMixedRoadmapProperRow.creating hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

private theorem parent_count (mode : Bool) (z : List Bool)
    (hc : 0<IntegralMixedRoadmapBadProbePacket.count (IntegralMixedRoadmapProperRow.oldPacket z)) :
    IntegralMixedMarkedPrefixFieldReadback.parent n (rr mode z)=rb z :=by
  unfold IntegralMixedMarkedPrefixFieldReadback.parent
  rw [IntegralMixedRoadmapProperRow.root_count hn ht ha hR0 mode z hc,
    IntegralMixedRoadmapProperRow.root_number hn ht ha hR0 mode z]
  rfl

theorem parent_values_equal (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic u))
    (HL : u∈language hn ht ha hR0 right) :
    ∃hO : SquareSampleCompleteVertices.Valid S (rc false (key u)) (ownWord false u),
    ∃hM : SquareSampleCompleteVertices.Valid S (rc true (key u)) (ownWord true u),
    ∀i<rb (key u),
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (rr false (key u)) (ownWord false u) hO i=
      IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
        (rr true (key u)) (ownWord true u) hM i :=by
  obtain ⟨hL,hO,HO⟩:=fieldMatch_sound hn ht ha hR0 false u HL.2.2.2.2.1
  obtain ⟨hL',hM,HM⟩:=fieldMatch_sound hn ht ha hR0 true u HL.2.2.2.2.2
  have HC:=IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (key u) hv
  refine ⟨hO,hM,fun i hi=>?_⟩
  have HCO:=IntegralMixedRoadmapProperRow.root_count hn ht ha hR0 false (key u) HC
  have HCM:=IntegralMixedRoadmapProperRow.root_count hn ht ha hR0 true (key u) HC
  have HPO:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (rr false (key u)) (ownWord false u) hO (HC.trans_eq HCO.symm) i
    (hi.trans_eq (parent_count hn ht ha hR0 false (key u) HC).symm)
  have HPM:=IntegralMixedMarkedPrefixFieldReadback.parent_chronological hn ht ha hR0
    (rr true (key u)) (ownWord true u) hM (HC.trans_eq HCM.symm) i
    (hi.trans_eq (parent_count hn ht ha hR0 true (key u) HC).symm)
  rw [parent_count hn ht ha hR0 false (key u) HC] at HPO
  rw [parent_count hn ht ha hR0 true (key u) HC] at HPM
  exact HPO.trans ((HO _ (by omega)).symm.trans ((HM _ (by omega)).trans HPM.symm))

noncomputable def commonSnapshot (z : List Bool):=
  IntegralMixedMarkedReservedBadSet.snapshot hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapProperRow.atomic z))
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProperRow.oldPacket z))
    (IntegralMixedRoadmapProperRow.code hn ht ha hR0 false z) []

private theorem snapshot_congr (a b : List Bool) (j : ℕ)
    (hca : j≤IntegralMixedCausalRecordPlanBits.count a) (hcb : j≤IntegralMixedCausalRecordPlanBits.count b)
    (he : a=b) : IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 a j hca=
      IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 b j hcb :=by
  cases he
  rfl

theorem commonSnapshot_eq_parent (z : List Bool) :commonSnapshot hn ht ha hR0 z=
    IntegralMixedRoadmapProperRow.parentSnapshot hn ht ha hR0 false z :=by
  unfold commonSnapshot IntegralMixedMarkedReservedBadSet.snapshot IntegralMixedRoadmapProperRow.parentSnapshot
  exact snapshot_congr hn ht ha hR0 _ _ _ _ _
    (IntegralMixedRoadmapProperRow.row_root_reserved hn ht ha hR0 false z).symm

theorem commonSnapshot_canonical (z : List Bool) :
    IntegralMixedHistory.Canonical (commonSnapshot hn ht ha hR0 z).state:=
  IntegralMixedMarkedReservedBadSet.canonical hn ht ha hR0 _ _ _ _

private theorem reserved_valid (mode : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (rc mode z) w) :
    SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (IntegralMixedMarkedPrefixRun.reservedRoot
        (IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapProperRow.atomic z))
        (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProperRow.oldPacket z))
        (IntegralMixedRoadmapProperRow.code hn ht ha hR0 mode z) [])) w :=by
  rw [IntegralMixedMarkedReservedPoint.input_eq]
  exact hv

attribute [local irreducible] IntegralMixedMarkedReservedBadSet.snapshot

theorem exists_common_interpretation (right : Bool) (u : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 (atomic u))
    (HL : u∈language hn ht ha hR0 right) :
    ∃hO : SquareSampleCompleteVertices.Valid S (rc false (key u)) (ownWord false u),
    ∃hM : SquareSampleCompleteVertices.Valid S (rc true (key u)) (ownWord true u),
    ∃φ : (commonSnapshot hn ht ha hR0 (key u)).state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((commonSnapshot hn ht ha hR0 (key u)).state.bank.numerator i)/
          ((commonSnapshot hn ht ha hR0 (key u)).state.bank.denominator i:ℝ)=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (rr false (key u)) (ownWord false u) hO i.val) ∧
      (∀i,φ ((commonSnapshot hn ht ha hR0 (key u)).state.bank.numerator i)/
          ((commonSnapshot hn ht ha hR0 (key u)).state.bank.denominator i:ℝ)=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (rr true (key u)) (ownWord true u) hM i.val) :=by
  obtain ⟨hO,hM,HE⟩:=parent_values_equal hn ht ha hR0 right u hv HL
  let hR:=reserved_valid hn ht ha hR0 false (key u) (ownWord false u) hO
  obtain ⟨φ,Hφ⟩:=IntegralMixedMarkedReservedBadSet.exists_interpretation hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapProperRow.atomic (key u)))
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProperRow.oldPacket (key u)))
    (IntegralMixedRoadmapProperRow.code hn ht ha hR0 false (key u)) [] (ownWord false u) hR
  have HP:=IntegralMixedMarkedReservedPoint.values_eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.candidate (IntegralMixedRoadmapProperRow.atomic (key u)))
    (IntegralMixedRoadmapBadProbePacket.prefixCodes (IntegralMixedRoadmapProperRow.oldPacket (key u)))
    (IntegralMixedRoadmapProperRow.code hn ht ha hR0 false (key u)) [] (ownWord false u) hR
  have HB : (commonSnapshot hn ht ha hR0 (key u)).birth=rb (key u):=by
    rw [commonSnapshot,IntegralMixedMarkedReservedBadSet.birth]
    simpa only [IntegralMixedRoadmapProperRow.parentBirth,IntegralMixedRoadmapProperRow.parentKey_root,
      IntegralMixedRoadmapProperRow.row_root_reserved] using
      IntegralMixedRoadmapProperRow.parentBirth_eq hn ht ha hR0 false (key u)
        (IntegralMixedRoadmapProperRow.row_count_positive hn ht ha hR0 (key u) hv)
  have HQ (i : Fin (commonSnapshot hn ht ha hR0 (key u)).birth) :
      φ ((commonSnapshot hn ht ha hR0 (key u)).state.bank.numerator i)/
          ((commonSnapshot hn ht ha hR0 (key u)).state.bank.denominator i:ℝ)=
        IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0
          (rr false (key u)) (ownWord false u) hO i.val:=
    (Hφ i).trans (congrFun HP i.val)
  exact ⟨hO,hM,φ,HQ,fun i=>(HQ i).trans (HE i.val (i.isLt.trans_eq HB))⟩

end LeanCanny.Encoding.IntegralMixedRoadmapProperRowWitness

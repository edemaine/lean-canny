/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixSnapshotFamily
public import LeanCanny.Encoding.IntegralMixedMarkedReservedBadSet
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeProvenance
/-! # Parent bad sets and native all-old-field agreement use only actual quotients -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)

private theorem bank_false :IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false=
    IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0):=rfl

noncomputable def snapshot (root : List Bool):=IntegralMixedMarkedPrefixSnapshot.snapshot hn ht ha hR0 root
 (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)

noncomputable def bad (root word labels : List Bool)
    (hv : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context root) word) :Set ℝ:=
 (snapshot hn ht ha hR0 root).bad labels (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 root word hv)

theorem birth (root : List Bool) (hc : 0<IntegralMixedCausalRecordPlanBits.count root) : (snapshot hn ht ha hR0 root).birth=IntegralMixedMarkedPrefixFieldReadback.parent n root:=by
 rw [snapshot,IntegralMixedMarkedPrefixSnapshot.birth]
 unfold IntegralMixedMarkedPrefixFieldReadback.parent
 omega

theorem snapshot_prepared (d : ℕ) (z : List Bool) (hc : 0<count (pairFst z)) :
    snapshot hn ht ha hR0 (root (pairFst z))=snapshot hn ht ha hR0 (preparedRoot d z):=by
 have HCL :IntegralMixedCausalRecordPlanBits.count (root (pairFst z))=count (pairFst z):=by
   simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,root,pairSnd_pair,pairFst_pair,count]
 have HCR:=prepared_count d z hc
 have HE:=IntegralMixedMarkedPrefixSnapshot.eq hn ht ha hR0 (root (pairFst z)) (preparedRoot d z)
   (by simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,root,preparedRoot,pairFst_pair])
   (HCL.trans HCR.symm) (IntegralMixedCausalRecordPlanBits.count (root (pairFst z))-1) (Nat.sub_le _ _)
   (by
     intro i hi
     have HI :i<count (pairFst z)-1:=by simpa only [HCL] using hi
     symm
     simpa only [IntegralMixedCausalRecordPlanBits.code,IntegralMixedCausalRecordPlanBits.records,
       root,preparedRoot,pairSnd_pair,pairFst_pair] using prepared_lookup d z i HI)
 unfold snapshot
 simpa only [HCL,HCR] using HE

theorem bad_eq_of_fields (d initial : ℕ) (z w : List Bool) (hc : 0<count (pairFst z))
    (hi : initial=(P).ambient (root (pairFst z))+5)
    (hl : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
    (hr : SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context (preparedRoot d z)) w)
    (hf : IntegralMixedRoadmapBadProbeFields.packet d initial z w∈IntegralMixedPhysicalFieldEqualityList.language hn ht ha (radius_binary hR0)) :
    bad hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) (labels (pairFst z)) hl=
      bad hn ht ha hR0 (preparedRoot d z) w (labels (pairFst z)) hr:=by
 have HV:=(IntegralMixedMarkedPrefixFieldReadback.packet_parent_iff hn ht ha hR0 d initial z w hc hi hl hr).mp hf
 have HB :(snapshot hn ht ha hR0 (root (pairFst z))).birth=creating initial (pairFst z):=by
   have HC :IntegralMixedCausalRecordPlanBits.count (root (pairFst z))=count (pairFst z):=by
     simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,root,pairSnd_pair,pairFst_pair,count]
   rw [birth hn ht ha hR0 _ (hc.trans_eq HC.symm)]
   unfold IntegralMixedMarkedPrefixFieldReadback.parent creating
   rw [HC,hi,IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0)]
 exact IntegralMixedPrefixSnapshot.Data.bad_transport _ _ (snapshot_prepared hn ht ha hR0 d z hc)
   (labels (pairFst z)) _ _ (fun i hi'=>HV i (hi'.trans_eq HB))

variable (z w : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
 (hb : IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false
   (pair (IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0) z) w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))

include hh hb in
theorem saved_snapshot :IntegralMixedPrefixSnapshot.ofState ((G).state old)=
    snapshot hn ht ha hR0 (preparedRoot (dim z) z):=by
 have HK:=IntegralMixedPhysicalCutLocalInterpretation.parent_saved hn ht ha (radius_binary hR0) false (ctx z) w hb
 have HR:=IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z
 have HC :0<IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z)):=by rw [HR,prepared_count _ z hh.1];exact hh.1
 have HM :(IntegralMixedPhysicalCutOpenInterval.birthWord (ctx z)).length=
     number n (pairFst (ctx z))+8+(IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z))-1):=by
   have HL:=IntegralMixedRoadmapBadProbeProvenance.last_birth hn ht ha hR0 z hh
   unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount at HL
   omega
 have HE:=congrArg (fun key=>IntegralMixedPrefixSnapshot.ofState ((G).state key)) HK
 rw [HM] at HE
 have HF:=IntegralMixedMarkedPrefixSnapshot.family_keyAt hn ht ha hR0 (pairFst (ctx z))
   (IntegralMixedCausalRecordPlanBits.count (pairFst (ctx z))-1) (Nat.sub_le _ _) (BinaryNatCode.encode 2)
 exact HE.trans (by
   rw [bank_false hn ht ha hR0]
   simpa only [HR,snapshot,IntegralMixedAuxiliaryMarkedRecordPlan.bank] using HF)

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeParent

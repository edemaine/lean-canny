/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbePreparedWord
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeCodedTransport
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRootAcceptance
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeSound
public import LeanCanny.Encoding.IntegralMixedPrefixSnapshotCodedHint
/-! # Chosen ordinary factors produce actual complete native probe witnesses -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeComplete
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits IntegralMixedRoadmapBadProbePacket
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralFramedPhysicalSquare.input
 IntegralFramedPhysicalSquare.point IntegralMixedPhysicalCutOpenInterval.parent IntegralMixedVirtualTaskBits.saved
 IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedRoadmapBadProbeParent.snapshot
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
local notation "EP"=>IntegralMixedPhysicalCutOrderedInterval.endpoint hn ht ha (radius_binary hR0) false
variable (z : List Bool) (codes : List (List Bool)) (last : List Bool)
 (hraw :raw (pairFst z)=WordList.encode (codes++[last]))
 (hl :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
   (IntegralMixedMarkedPrefixFieldReadback.context (root (pairFst z))) (word (pairFst z)))
local notation "VL"=>IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root (pairFst z)) (word (pairFst z)) hl

include hraw in
theorem at_hint (a : ℝ)
    (hh : HintGood (dim z) (ini z) (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
    (hcoded : (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).CodedFactor
      (labels (pairFst z)) VL a (probe (dim z) z))
    (hd :Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).ambient+1)
      (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root (pairFst z))).source.degree)
    (ha' :a∈Set.Ioo (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (pairFst z) hl false)
      (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (pairFst z) hl true)) :
    ∃w,IntegralMixedRoadmapBadProbeTest.Witness hn ht ha (radius_binary hR0) (pair z w):=by
 obtain ⟨w,hw,HF⟩:=IntegralMixedRoadmapBadProbePreparedWord.exists_fields hn ht ha hR0 z codes last hraw hh hl hd
 let VR:=IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (preparedRoot (dim z) z) w hw
 have HC:=IntegralMixedRoadmapBadProbeCodedTransport.actual hn ht ha hR0 z w hh hl hw a HF hcoded
 have HR:=IntegralMixedRoadmapBadProbeRuntime.receipt hn ht ha hR0 z hh VR a HC
 have HB:=IntegralMixedRoadmapBadProbeRuntime.bounds hn ht ha hR0 z hh w HR.1
 have HV :SquareSampleCompleteVertices.Valid S (ctx z) w:=
   (IntegralMixedPhysicalMarkedContext.valid_iff hn ht ha (radius_binary hR0)
     (IntegralMixedMarkedPrefixFieldReadback.context (preparedRoot (dim z) z)) (ctx z) w
     ((pairFst_pair _ _).trans (IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z).symm)).mp hw
 have HVal:=IntegralMixedRoadmapBadProbePresence.parent_values hn ht ha hR0 z w HV
 have HR' :(IntegralMixedCutCreationReceipt.native P D H
     (IntegralMixedVirtualTaskBits.saved P (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z)))).HasRoot
     (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (pairFst (ctx z)) w
       (IntegralMixedPhysicalCutParentPoint.empty_valid hn ht ha hR0 (ctx z) w HV)) a:=
   (congrArg (fun values=>(IntegralMixedCutCreationReceipt.native P D H
     (IntegralMixedVirtualTaskBits.saved P (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z)))).HasRoot values a) HVal).mpr HR.2
 have HE :∀side,∀hi:IntegralMixedPhysicalCutOpenInterval.selected side (ctx z)<
     IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (ctx z),
     EP side (ctx z) w HV hi=IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 (pairFst z) hl side:=by
   intro side hi
   have HP:=IntegralMixedRoadmapBadProbeEndpoint.producer_bound hn ht ha hR0 z hh side
   have HI :creating (ini z) (pairFst z)-1-producer side (pairFst z)<creating (ini z) (pairFst z):=by omega
   have HE:=IntegralMixedRoadmapBadProbeEndpoint.endpoint_parent hn ht ha hR0 z w hh HV side hi
   exact HE.trans ((congrFun HVal _).trans (HF _ HI).symm)
 have HU :a∈Set.Ioo (EP false (ctx z) w HV (IntegralMixedPhysicalCutOrderedInterval.left_bound hn ht ha (radius_binary hR0) false (ctx z) w HB))
     (EP true (ctx z) w HV (IntegralMixedPhysicalCutOrderedInterval.right_bound hn ht ha (radius_binary hR0) false (ctx z) w HB)):=by
   rw [HE false,HE true]
   exact ha'
 obtain ⟨HG,HNo⟩:=IntegralMixedRoadmapBadProbeRootAcceptance.accepted hn ht ha hR0 z w hh HV HB a HU HR'
 have HFields:=(IntegralMixedMarkedPrefixFieldReadback.packet_parent_iff hn ht ha hR0 (dim z) (ini z) z w hh.1 rfl hl hw).mpr HF
 refine ⟨w,?_,?_,?_,?_,?_,?_⟩
 · simpa only [pairFst_pair] using hh
 · simpa only [IntegralMixedRoadmapBadProbeTest.fieldPacket,pairFst_pair,pairSnd_pair,
     IntegralMixedRoadmapBadProbeFields.packet,IntegralMixedRoadmapBadProbeFields.leftContext,
     IntegralMixedRoadmapBadProbeFields.rightContext] using HFields
 · simpa only [pairFst_pair,pairSnd_pair] using HV
 · simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using HB
 · simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using HG
 · simpa only [IntegralMixedRoadmapBadProbeTest.intervalPacket,pairFst_pair,pairSnd_pair] using HNo

theorem at_hint_base (base : List Bool) (hb :pairFst z=base)
    (hrawB :raw base=WordList.encode (codes++[last]))
    (hbase :SquareSampleCompleteVertices.Valid S (IntegralMixedMarkedPrefixFieldReadback.context (root base)) (word base))
    (a : ℝ)
    (hh : HintGood (dim z) (ini z) (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
    (hcoded : (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root base)).CodedFactor
      (labels base) (IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (root base) (word base) hbase)
      a (probe (dim z) z))
    (hd :Nat.fromBitsLE (field 3 z)≤IntegralMixedExceptionalBounds.auxiliaryCap
      ((IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root base)).ambient+1)
      (IntegralMixedRoadmapBadProbeParent.snapshot hn ht ha hR0 (root base)).source.degree)
    (ha' :a∈Set.Ioo (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 base hbase false)
      (IntegralMixedRoadmapBadProbeSound.endpoint hn ht ha hR0 base hbase true)) :
    ∃w,IntegralMixedRoadmapBadProbeTest.Witness hn ht ha (radius_binary hR0) (pair z w):=by
 subst base
 exact at_hint hn ht ha hR0 z codes last hrawB hbase a hh hcoded hd ha'

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeComplete

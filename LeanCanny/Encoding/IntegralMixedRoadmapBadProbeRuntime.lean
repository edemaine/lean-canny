/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeTask
public import LeanCanny.Encoding.IntegralMixedRoadmapBadProbeEndpoint
/-! # Actual chosen bytes derive runtime cut bounds without a guard oracle -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRuntime
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedRoadmapBadProbePacket
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
private def SelectedProperty (b : IntegralFramedBankQuery.Bank) (key code labels : List Bool) (values : ℕ→ℝ) (a : ℝ):Prop:=
 (IntegralMixedPrefixSnapshot.ofState ((family b.parameters b.plan b.data).state key)).CodedFactor labels values a code→
   IntegralMixedCutCreationReceipt.atKey b.parameters b.plan b.data key=some (IntegralMixedCutCreationReceipt.native b.parameters b.plan b.data key) ∧
     (IntegralMixedCutCreationReceipt.native b.parameters b.plan b.data key).HasRoot values a

variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
local notation "ctx"=>IntegralMixedRoadmapBadProbeTest.intervalContext hn ht ha (radius_binary hR0)
local notation "dim"=>IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0)
local notation "ini"=>IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0)
private theorem banks_equal :IntegralMixedMarkedReservedParent.bank hn ht ha hR0=(B):=rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

variable (z : List Bool)
 (hh : HintGood (IntegralMixedRoadmapBadProbeTest.dimension hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.initial hn ht ha (radius_binary hR0) z)
   (IntegralMixedRoadmapBadProbeTest.width hn ht ha (radius_binary hR0) z) z)
local notation "old"=>IntegralMixedVirtualTaskBits.saved P
 (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z))

include hh in
theorem prefix_length :prefixLength P old=number n (pairFst old)+8+(prefixCodes (pairFst z)).length:=by
 have HE:=congrArg (prefixLength P) (IntegralMixedRoadmapBadProbeTask.saved hn ht ha hR0 z hh)
 have HP:=keyAt_prefix P (preparedRoot (dim z) z) (creating (ini z) (pairFst z)) (BinaryNatCode.encode 2)
   (IntegralMixedRoadmapBadProbeTask.stage_cap hn ht ha hR0 z hh)
 exact HE.trans (HP.trans (IntegralMixedRoadmapBadProbeProvenance.creating_saved hn ht ha hR0 z hh))

include hh in
theorem receipt (values : ℕ→ℝ) (a : ℝ)
    (hcoded : (IntegralMixedPrefixSnapshot.ofState ((G).state old)).CodedFactor (labels (pairFst z)) values a (probe (dim z) z)) :
    IntegralMixedCutCreationReceipt.atKey P D H old=some (IntegralMixedCutCreationReceipt.native P D H old) ∧
      (IntegralMixedCutCreationReceipt.native P D H old).HasRoot values a:=by
 have HT:=IntegralMixedRoadmapBadProbeProvenance.records_saved hn ht ha hR0 z
 rw [IntegralMixedRoadmapBadProbeProvenance.dimension_saved hn ht ha hR0 z] at HT
 have HK :prefixLength (IntegralMixedMarkedReservedParent.bank hn ht ha hR0).parameters old=
     number n (pairFst old)+8+(prefixCodes (pairFst z)).length:=
   (congrArg (fun b : IntegralFramedBankQuery.Bank=>prefixLength b.parameters old) (banks_equal hn ht ha hR0)).trans
     (prefix_length hn ht ha hR0 z hh)
 have HP :SelectedProperty (IntegralMixedMarkedReservedParent.bank hn ht ha hR0) old (probe (dim z) z)
     (labels (pairFst z)) values a:=
   IntegralMixedMarkedReservedSelectionReceipt.native_receipt hn ht ha hR0 old (prefixCodes (pairFst z))
     (probe (dim z) z) (labels (pairFst z)) values a HT HK
 exact ((congrArg (fun b : IntegralFramedBankQuery.Bank=>SelectedProperty b old (probe (dim z) z)
   (labels (pairFst z)) values a) (banks_equal hn ht ha hR0)).mp HP) hcoded

include hh in
theorem count :IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (ctx z)=creating (ini z) (pairFst z)+1:=by
 change IntegralMixedPhysicalFieldEquality.count hn ht ha (radius_binary hR0) (ctx z)=_
 rw [IntegralMixedPhysicalFieldEquality.count_eq,IntegralMixedRoadmapBadProbeProvenance.context_root hn ht ha hR0 z]
 unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
 rw [prepared_count _ z hh.1,IntegralMixedRoadmapBadProbeFields.prepared_number]
 have HI :ini z=number n (root (pairFst z))+8:=IntegralMixedRoadmapBadProbeFields.initial_eq hn ht ha (radius_binary hR0) (pairFst z)
 unfold creating
 rw [HI]
 have HC:=hh.1
 omega

include hh in
theorem bounds (w : List Bool)
    (hcut :IntegralMixedCutCreationReceipt.atKey P D H old=some (IntegralMixedCutCreationReceipt.native P D H old)) :
    IntegralMixedPhysicalCutOpenInterval.Bounds hn ht ha (radius_binary hR0) false (pair (ctx z) w):=by
 have HCount:=count hn ht ha hR0 z hh
 have HS :∀side,IntegralMixedPhysicalCutOpenInterval.selected side (ctx z)<
     IntegralMixedPhysicalCutOpenInterval.count hn ht ha (radius_binary hR0) false (ctx z):=by
   intro side
   rw [IntegralMixedRoadmapBadProbeEndpoint.selected_index hn ht ha hR0 z side,HCount]
   omega
 refine ⟨?_,?_,?_,?_⟩
 · simpa only [pairFst_pair] using HS false
 · simpa only [pairFst_pair] using HS true
 · simpa only [pairFst_pair,IntegralMixedRoadmapBadProbeProvenance.context_birth hn ht ha hR0 z,HCount] using Nat.lt_succ_self (creating (ini z) (pairFst z))
 · change IntegralFramedCreatingCut.ParentCut P D
     (IntegralFramedTraceCutGuards.parent P (IntegralMixedPhysicalCutOpenInterval.guardPacket (pair (ctx z) w)))
   have HE :IntegralFramedTraceCutGuards.parent P (IntegralMixedPhysicalCutOpenInterval.guardPacket (pair (ctx z) w))=
       IntegralMixedPhysicalCutOpenInterval.parent hn ht ha (radius_binary hR0) false (ctx z):=by
     simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
       IntegralFramedTraceCutGuards.root,IntegralMixedPhysicalCutOpenInterval.guardPacket,
       IntegralMixedPhysicalCutOpenInterval.parent,pairFst_pair,pairSnd_pair]
   rw [HE]
   exact IntegralMixedCutCreationReceipt.atKey_isCut P D H old _ hcut

end LeanCanny.Encoding.IntegralMixedRoadmapBadProbeRuntime

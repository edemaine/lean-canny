/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedProperMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapChainSeedTail
/-! # Every checked seed-padding record selects coordinate zero -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapCheckedSeedSelected
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem raw_seed_get {d B sourceCap initial C : ℕ} {q : List Bool}
    (hc : IntegralMixedRoadmapChain.Checked d B sourceCap initial C q)
    (hp : IntegralMixedRoadmapChain.probe q=IntegralMixedRoadmapChain.seedCode d)
    (i : ℕ) (hi : IntegralMixedRoadmapChain.rawStart d q (IntegralMixedRoadmapChain.depth q) ≤ i)
    (hj : i < WordListRecords.count (IntegralMixedRoadmapChain.raw q)) :
    WordList.get (IntegralMixedRoadmapChain.raw q) i=IntegralMixedRoadmapChain.seedCode d :=by
  have HR:=IntegralMixedRoadmapChain.raw_seed_tail hc hp
  have HL:=IntegralMixedRoadmapChain.meaningfulCodes_length d q
  have HB : i-(IntegralMixedRoadmapChain.meaningfulCodes d q).length<
      IntegralMixedRoadmapChain.paddingCount d q+1:=by
    rw [HR,WordListRecords.count_encode,List.length_append,List.length_replicate] at hj
    omega
  rw [HR,WordList.get_encode,List.getElem?_append_right (by omega)]
  simp only [List.getElem?_replicate,HB,ite_true,Option.getD_some]

private theorem empty_point_good (d b : ℕ) : IntegralMixedChronologicalFrameCode.PointGood d b [] 0 0 :=by
  simp [IntegralMixedChronologicalFrameCode.PointGood,IntegralMixedChronologicalFrameCode.Good,
    WordListRecords.count]

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "I"=>IntegralMixedRoadmapAtomic.initial hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.root
  IntegralMixedRoadmapSeedMetadata.stageHeader

variable (q :List Bool)
  (H :IntegralMixedRoadmapChain.Checked (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
    (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q)
    (IntegralMixedRoadmapAtomic.payload q))
  (hp :IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q)=
    IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q))

include H hp in
theorem seed_code_after_end (b :ℕ)
    (hb0 :IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))):
    IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) (b-I q)=
      IntegralMixedRoadmapChain.seedCode (D q):=by
  have HF:=IntegralMixedRoadmapCheckedProperMetadata.full_prefix hn ht ha hR0 q
  rw [HF] at hb1
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [IntegralMixedRoadmapCheckedProperMetadata.root_records]
  apply raw_seed_get H hp
  · change I q+IntegralMixedRoadmapChain.rawStart (D q) (IntegralMixedRoadmapAtomic.payload q)
      (IntegralMixedRoadmapChain.depth (IntegralMixedRoadmapAtomic.payload q))≤b at hb0
    omega
  · have H0 :I q≤b:=by unfold IntegralMixedRoadmapAtomic.endBirth at hb0;omega
    omega

include H hp in
theorem selected_after_end (b :ℕ)
    (hb0 :IntegralMixedRoadmapAtomic.endBirth (D q) (I q) q≤b)
    (hb1 :b<IntegralMixedFramedHistoryFamilyBits.prefixLength (B).parameters ((B).key (IntegralMixedRoadmapAtomic.context q))):
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
      (IntegralMixedRoadmapAtomic.context q) b=0:=by
  let idx:=b-I q
  have H0 :I q≤b:=by unfold IntegralMixedRoadmapAtomic.endBirth at hb0;omega
  have HI0:=IntegralMixedRoadmapCheckedProperMetadata.root_initial hn ht ha hR0 q
  have HB :b=number n (IntegralMixedRoadmapAtomic.root q)+8+idx:=by dsimp only [idx];omega
  have HI :idx<IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root q):=by
    have HF:=IntegralMixedRoadmapCheckedProperMetadata.full_prefix hn ht ha hR0 q
    rw [HF] at hb1
    unfold IntegralMixedCausalRecordPlanBits.count
    rw [IntegralMixedRoadmapCheckedProperMetadata.root_records]
    dsimp only [idx]
    omega
  have HG:=empty_point_good ((P).ambient (IntegralMixedRoadmapAtomic.root q))
    (number n (IntegralMixedRoadmapAtomic.root q)+8+idx)
  have HW :IntegralMixedCausalRecordPlanBits.code (IntegralMixedRoadmapAtomic.root q) idx=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (IntegralMixedRoadmapAtomic.root q)) [] 0 0:=by
    rw [IntegralMixedRoadmapCheckedProperMetadata.root_dimension hn ht ha hR0 q]
    exact seed_code_after_end hn ht ha hR0 q H hp b hb0 hb1
  have HC:=IntegralMixedMarkedRecordReceipt.critical hn ht ha hR0 (IntegralMixedRoadmapAtomic.root q)
    idx HI [] 0 0 HG HW
  rw [HB]
  unfold IntegralMixedPhysicalPointCompanionScan.selected
  rw [IntegralMixedRoadmapCheckedProperMetadata.native_header hn ht ha hR0 q]
  unfold IntegralMixedRoadmapSeedMetadata.stageHeader
  rw [HC]
  exact IntegralMixedChronologicalFrame.raw_selected _ [] 0 0 HG

end LeanCanny.Encoding.IntegralMixedRoadmapCheckedSeedSelected

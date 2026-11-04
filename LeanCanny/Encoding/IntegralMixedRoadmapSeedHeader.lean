/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadataCode
public import LeanCanny.Algebra.IntegralMixedStaticRecordHeaderReceipt
public import LeanCanny.Encoding.IntegralMixedMarkedRecordReceipt
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
/-! # Actual original seed histories contain only integer and critical records -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
local notation "DIM" old=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
local notation "ROOT" old=>IntegralMixedRoadmapSeedResampling.preparedRoot hn ht ha hR0 old
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerSource.source
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedRoadmapAtomic.dimension

noncomputable def stageHeader (root : List Bool) (b : ℕ) :=IntegralMixedCommandHeaderBits.command
  (IntegralMixedFramedRootPullback.instructionAt P D root b).command

theorem stageHeader_records (root : List Bool) (b : ℕ) : stageHeader hn ht ha hR0 root b=
    (((IntegralMixedMarkedPrefixRecords.records hn ht ha hR0 root).reverse[b]?).map
      (fun r=>r.template.header)).getD IntegralMixedCommandHeaderBits.zero :=by
  unfold stageHeader IntegralMixedFramedRootPullback.instructionAt
  rw [IntegralMixedMarkedPrefixRecords.rules hn ht ha hR0 root]
  exact IntegralMixedStaticRecordHeaderReceipt.commands_header _ _ _ _ _

theorem prelude_header (root : List Bool) (b : ℕ) (hb : b<number n root+8) :
    stageHeader hn ht ha hR0 root b=IntegralMixedCommandHeaderBits.zero :=by
  rw [stageHeader_records]
  exact IntegralMixedStaticRecordHeaderReceipt.integer_header (Q root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root) (number n root+8)
    (IntegralMixedCausalRecordPlanBits.count root)
    (IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root)
    (IntegralMixedCausalRecordPlanBits.code root) b hb

theorem later_header (root : List Bool) (a : ℕ) (ha0 : a<IntegralMixedCausalRecordPlanBits.count root) :
    stageHeader hn ht ha hR0 root (number n root+8+a)=
      (IntegralMixedCausalUnitRecordBits.record (Q root)
        (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root) (number n root+8+a)
        (IntegralMixedCausalRecordPlanBits.code root a)
        (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root)).template.header :=by
  rw [stageHeader_records]
  exact IntegralMixedStaticRecordHeaderReceipt.later_header (Q root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha root)
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 root) (number n root+8)
    (IntegralMixedCausalRecordPlanBits.count root)
    (IntegralMixedMarkedPrefixRecords.polynomial hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_nonzero hn ht ha (R0:=R0) root)
    (IntegralMixedMarkedPrefixRecords.polynomial_degree hn ht ha hR0 root)
    (IntegralMixedCausalRecordPlanBits.code root) a ha0

theorem dimension_root (old : List Bool) : (P).ambient (ROOT old)=DIM old :=by
  change number n (ROOT old)+3=_
  rw [IntegralMixedRoadmapAtomic.dimension_eq hn ht ha hR0 old]
  simp only [number,IntegralMixedAuxiliaryMarkedIntegerSource.original,IntegralMixedAuxiliaryMarkedIntegerSource.candidate,
    IntegralMixedRoadmapSeedResampling.preparedRoot,IntegralMixedRoadmapAtomic.root,
    IntegralMixedRoadmapSeedResampling.candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem initial_root (old : List Bool) : number n (ROOT old)+8=(DIM old)+5:=by
  have HE:=dimension_root hn ht ha hR0 old
  change number n (ROOT old)+3=DIM old at HE
  omega

theorem records_root (old : List Bool) : IntegralMixedCausalRecordPlanBits.records (ROOT old)=
    IntegralMixedRoadmapChain.raw (IntegralMixedRoadmapSeedResampling.payload (DIM old)) :=by
  simp only [IntegralMixedCausalRecordPlanBits.records,IntegralMixedRoadmapSeedResampling.preparedRoot,
    IntegralMixedRoadmapAtomic.root,IntegralMixedRoadmapSeedResampling.payload_packet,pairSnd_pair,pairFst_pair]

theorem code_root (old : List Bool) (a : ℕ) (ha0 : a<IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    IntegralMixedCausalRecordPlanBits.code (ROOT old) a=
      IntegralMixedChronologicalFrameCode.code (DIM old) [] 0 (selected (DIM old) a) :=by
  unfold IntegralMixedCausalRecordPlanBits.code
  rw [records_root]
  exact raw_lookup (DIM old) a (by
    simpa only [IntegralMixedCausalRecordPlanBits.count,records_root] using ha0)

private theorem empty_rule_header {n birth B : ℕ} (S : SpatialSource n) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) S.degree≤2^B)
    (j : ℕ) (hj : j<n+1) :
    (IntegralMixedCausalUnitRecordBits.record S hn birth
      (IntegralMixedChronologicalFrameCode.code n [] 0 j) hcap).template.header=
      (⟨1,j,0,0,0,0,1⟩ : IntegralMixedCommandHeaderBits.Header) :=by
  have HG:=IntegralMixedRoadmapChain.seed_point_good n birth j hj
  have HC:=IntegralMixedChronologicalFrameCode.raw_command S hn [] 0 j HG hcap 1 one_ne_zero
  have HE:=congrArg IntegralMixedCommandHeaderBits.command HC
  change (IntegralMixedCausalUnitRecordBits.record S hn birth
    (IntegralMixedChronologicalFrameCode.code n [] 0 j) hcap).template.header=_ at HE
  rw [HE]
  let dd:=IntegralMixedChronologicalFrameCode.descriptor n birth [] HG.1
  have HF : dd.frame.frozen.card=0:=by
    rw [dd.frozen_card,IntegralMixedChronologicalFrameCode.descriptor_length]
    exact WordListRecords.count_encode []
  have HP : FrozenCoordinateOrdering.permutation dd.frame.frozen=Equiv.refl (Fin (n+1)):=dd.prefix_frozen.permutation
  have HZ : ∀i : Fin (n+1),i∉dd.frame.frozen:=by
    intro i
    rw [dd.frozen_mem,IntegralMixedChronologicalFrameCode.descriptor_length]
    rw [show WordListRecords.count ([] : List Bool)=0 from WordListRecords.count_encode []]
    omega
  change (⟨1,(IntegralMixedFrozenFrame.freeCoordinate dd.frame ⟨j,hj⟩ (HZ _)).val%(n-dd.frame.frozen.card+1),
    dd.frame.frozen.card,(IntegralMixedFrozenFrame.freeCoordinate dd.frame ⟨0,by omega⟩ (HZ _)).val,0,0,1⟩ :
      IntegralMixedCommandHeaderBits.Header)=⟨1,j,0,0,0,0,1⟩
  simp only [IntegralMixedFrozenFrame.freeCoordinate,HF,HP,Equiv.refl_symm,Equiv.refl_apply,
    Nat.sub_zero,Nat.mod_eq_of_lt hj]

theorem seed_header (old : List Bool) (a : ℕ) (ha0 : a<IntegralMixedCausalRecordPlanBits.count (ROOT old)) :
    stageHeader hn ht ha hR0 (ROOT old) (number n (ROOT old)+8+a)=
      (⟨1,selected (DIM old) a,0,0,0,0,1⟩ : IntegralMixedCommandHeaderBits.Header) :=by
  rw [later_header hn ht ha hR0 _ _ ha0,code_root hn ht ha hR0 old a ha0]
  have HN:=dimension_root hn ht ha hR0 old
  have HC : IntegralMixedChronologicalFrameCode.code (DIM old) [] 0 (selected (DIM old) a)=
      IntegralMixedChronologicalFrameCode.code ((P).ambient (ROOT old)) [] 0 (selected (DIM old) a):=by rw [HN]
  rw [HC]
  exact empty_rule_header _ _ _ _ (by
    change selected (DIM old) a<(P).ambient (ROOT old)+1
    rw [HN]
    exact selected_lt _ _)

end LeanCanny.Encoding.IntegralMixedRoadmapSeedMetadata

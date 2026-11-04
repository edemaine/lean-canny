/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastValues
public import LeanCanny.Encoding.IntegralMixedMarkedCriticalNatural
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixCriticalMetadata
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedHeader
/-! # Historical critical correlations survive a proper append

Each root has its own complete word. Only the literal old natural columns
are retained; no ordinal is transported between samplers.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
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
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedRoadmapAtomic.root IntegralMixedRoadmapAtomic.payload IntegralMixedRoadmapAtomic.depth
  IntegralMixedRoadmapAtomic.dimension IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.endBirth
  preparedRoot start IntegralMixedMarkedPrefixObservation.observation IntegralMixedPhysicalFieldEquality.point

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right)

private theorem full_prefix (root :List Bool):prefixLength P ((B).key (CTX root))=
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root:=by
  have HC:=IntegralMixedPhysicalFieldEquality.count_eq hn ht ha (radius_binary hR0) (CTX root)
  simp only [IntegralMixedMarkedPrefixFieldReadback.context,pairFst_pair] at HC
  exact (IntegralMixedFramedHistoryFamilyBits.family_birth P D H _).symm.trans HC

private theorem active_iff_header (root :List Bool) (b :ℕ)
    (hb :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root) :
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX root) b↔
      (IntegralMixedMarkedPrefixCriticalMetadata.header hn ht ha hR0 root b).context=1:=by
  simp only [IntegralMixedPhysicalPointCompanionScan.Active,IntegralMixedFramedCriticalGuardBits.Active,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate]
  change (b<prefixLength P ((B).key (CTX root)) ∧
    (IntegralMixedMarkedPrefixCriticalMetadata.header hn ht ha hR0 root b).context=1)↔_
  rw [full_prefix hn ht ha hR0 root]
  simp only [hb,true_and]

private theorem prefix_arity_observation (root :List Bool) (j :ℕ)
    (hj :j≤IntegralMixedCausalRecordPlanBits.count root) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T
      (pair ((B).key (CTX root)) (List.replicate (number n root+8+j) true))=
      (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj).arity:=by
  have HR :pairFst ((B).key (CTX root))=root:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  rw [IntegralMixedFramedPhysicalIndex.prefixArity_packet P D H T
    (IntegralMixedPhysicalMarkedPlan.represents hn ht ha (radius_binary hR0) false),HR]
  unfold IntegralMixedMarkedPrefixObservation.observation IntegralMixedPhysicalMarkedPlan.bank
  rfl

private theorem critical_column_bound (root :List Bool) (b bound :ℕ) (hbound :b<bound)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false (CTX root) b) :
    IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b <
      IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate bound true)):=by
  have HS:=IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false (CTX root) b hb
  have HA:=(IntegralMixedPhysicalPointCompanionScan.active_direct hn ht ha (radius_binary hR0) false (CTX root) b hb).2
  have HR :pairFst ((B).key (CTX root))=root:=by
    rw [IntegralMixedPhysicalFieldEquality.key_root]
    exact pairFst_pair _ _
  have HSpan :IntegralMixedFramedPhysicalIndex.span P T (pair ((B).key (CTX root)) (List.replicate b true))=
      IntegralMixedFramedPhysicalIndex.block ((P).ambient root)+1:=by
    unfold IntegralMixedFramedPhysicalIndex.span
    unfold IntegralMixedFramedCriticalGuardBits.header at HA
    simp only [pairFst_pair,pairSnd_pair,List.length_replicate,HR] at HA ⊢
    rw [ite_eq_left HA]
  have H1 :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate b true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX root) b <
      IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX root)) (List.replicate (b+1) true)):=by
    rw [IntegralMixedFramedPhysicalRowSelector.prefix_succ,HSpan]
    rw [HR] at HS
    unfold IntegralMixedFramedPhysicalIndex.block
    omega
  exact H1.trans_le ((IntegralMixedFramedPhysicalRowSelector.prefix_strictMono P T ((B).key (CTX root))).monotone (by omega))

include hd hE in
/-- A historical critical birth is checked on the NEW word using exactly its
preserved old natural columns. The old word supplies the old accepted guard. -/
theorem past_critical_raw_stage (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old left right side)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old left right side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old left right side) w hw r=
        oldNatural hn ht ha hR0 old hv r)
    (j :ℕ) (hj :j<start hn ht ha hR0 old)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) (number n (IntegralMixedRoadmapAtomic.root old)+8+j)) :
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) w hw (number n (IntegralMixedRoadmapAtomic.root old)+8+j) hb=
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) w hw (number n (IntegralMixedRoadmapAtomic.root old)+8+j)
      ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
        (CTX (preparedRoot hn ht ha hR0 old left right side)) (number n (IntegralMixedRoadmapAtomic.root old)+8+j),
        IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩:=by
  let r:=preparedRoot hn ht ha hR0 old left right side
  let l:=IntegralMixedRoadmapAtomic.root old
  let b:=number n l+8+j
  have HC:=prepared_candidate hn ht ha hR0 old left right side
  have HCount:=prepared_count hn ht ha hR0 old hv hd left right side hE
  have HN :number n r=number n l:=IntegralMixedMarkedPreludeCongruence.number_eq r l HC
  have HFitR :=(start_fit hn ht ha hR0 old hv).trans_eq HCount.symm
  have HJL :j+1≤IntegralMixedCausalRecordPlanBits.count r:=(Nat.succ_le_of_lt hj).trans HFitR
  have HCode :∀i,i<j+1→IntegralMixedCausalRecordPlanBits.code r i=IntegralMixedCausalRecordPlanBits.code l i:=by
    intro i hi
    exact prepared_record hn ht ha hR0 old hv left right side i (hi.trans_le (Nat.succ_le_of_lt hj))
  have HH:=IntegralMixedMarkedPrefixCriticalMetadata.header_eq hn ht ha hR0 r l HC HCount j HJL HCode
  rw [HN] at HH
  have HBLeft :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    rw [HN,HCount]
    have HF:=start_fit hn ht ha hR0 old hv
    dsimp only [b,l]
    omega
  have HBRight :b<IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n l:=by
    unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
    have HF:=start_fit hn ht ha hR0 old hv
    dsimp only [b,l]
    omega
  have HAnew:=(active_iff_header hn ht ha hR0 r b HBLeft).mp hb
  have HAold :(IntegralMixedMarkedPrefixCriticalMetadata.header hn ht ha hR0 l b).context=1:=
    (congrArg IntegralMixedCommandHeaderBits.Header.context HH).symm.trans HAnew
  have hbo:=(active_iff_header hn ht ha hR0 l b HBRight).mpr HAold
  have HS :IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX r) b=
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX l) b:=by
    simpa only [IntegralMixedPhysicalPointCompanionScan.selected,IntegralMixedMarkedPrefixCriticalMetadata.header]
      using congrArg (fun h :IntegralMixedCommandHeaderBits.Header=>h.offset+h.coordinate) HH
  have HAr:=IntegralMixedMarkedPrefixCriticalMetadata.arity_eq hn ht ha hR0 r l HC HCount j
    (Nat.le_trans (Nat.le_of_lt hj) HFitR) (fun i hi=>HCode i (by omega))
  rw [HN] at HAr
  let col:=IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX l)) (List.replicate b true))+
    IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX l) b
  have HCol :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX r)) (List.replicate b true))+
      IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX r) b=col:=
    congrArg₂ (·+·) HAr HS
  have HColBound :col<(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 l
      (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)).arity:=by
    have HB0 :b<number n l+8+start hn ht ha hR0 old:=by dsimp only [b];omega
    exact (critical_column_bound hn ht ha hR0 l b _ HB0 hbo).trans_eq
      (prefix_arity_observation hn ht ha hR0 l (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv))
  have HRaw:=past_raw_native hn ht ha hR0 old hv hd left right side hE _ hr col HColBound
  have HRaw' :IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw
      (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX r)) (List.replicate b true))+
        IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX r) b)=
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 l (IntegralMixedRoadmapAtomic.word old)
        (old_valid_native hn ht ha hR0 old hv) col:=
    (congrArg (IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw) HCol).trans HRaw
  have HCap :(P).cap r=(P).cap l:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r l HC HCount
  have HWidth :(P).width r=(P).width l:=by
    unfold IntegralMixedPhysicalMarkedPlan.bank
    exact IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r l HC
  have HPow :UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=
      UniformIntegralPowerSchedule.physical ((P).cap l+1) (2^(P).width l) b:=
    congrArg₂ (fun s d=>UniformIntegralPowerSchedule.physical (s+1) (2^d) b) HCap HWidth
  have HPacket :pair l (IntegralMixedRoadmapAtomic.word old)∈
      IntegralMixedPhysicalGuardScan.language hn ht ha (radius_binary hR0) false:=hv.2.2.2.2.1
  obtain ⟨hwOld,HOld⟩:=(IntegralMixedPhysicalPointCompanionScan.all_critical_packet_iff hn ht ha (radius_binary hR0) false
    l (IntegralMixedRoadmapAtomic.word old)).mp HPacket
  have HSign :IntegralMixedPhysicalPointCompanionScan.scalarValue hn ht ha (radius_binary hR0) false
      (CTX l) (IntegralMixedRoadmapAtomic.word old) b=InfinitesimalSign.encode 0:=by
    apply (IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_iff hn ht ha (radius_binary hR0) false
      (CTX l) (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) b hbo).mpr
    exact HOld b (by
      change b<prefixLength P ((B).key (CTX l))
      rw [full_prefix hn ht ha hR0 l]
      exact HBRight) hbo
  have HEqOld:=(IntegralMixedMarkedCriticalNatural.scalarValue_zero_iff hn ht ha hR0 l
    (IntegralMixedRoadmapAtomic.word old) (old_valid_native hn ht ha hR0 old hv) b hbo).mp HSign
  have HField:=past_fields hn ht ha hR0 old hv hd left right side hE w hw hr b (by
    rw [begin_eq_old_start hn ht ha hR0 old]
    dsimp only [b,l]
    omega)
  have HEqNew :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX r) w hw b=
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r w hw
        (IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key (CTX r)) (List.replicate b true))+
          IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false (CTX r) b)^
        UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b:=
    HField.trans (HEqOld.trans (congrArg₂ (fun (v :ℝ) (e :ℕ)=>v^e) HRaw' HPow).symm)
  exact (IntegralMixedPhysicalPointCompanionScan.scalarValue_zero_iff hn ht ha (radius_binary hR0) false
    (CTX r) w hw b hb).mp ((IntegralMixedMarkedCriticalNatural.scalarValue_zero_iff hn ht ha hR0 r w hw b hb).mpr HEqNew)

include hd hE in
/-- Every active critical birth before the proper append has its honest
correlation on the new root's own full word. Integer-prelude births are inactive. -/
theorem past_critical (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old left right side)) w)
    (hr :∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old left right side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old left right side) w hw r=
        oldNatural hn ht ha hR0 old hv r)
    (b :ℕ) (hb :b<beginBirth hn ht ha hR0 old)
    (ha0 :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) b) :
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) w hw b ha0=
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false
      (CTX (preparedRoot hn ht ha hR0 old left right side)) w hw b
      ⟨IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false
        (CTX (preparedRoot hn ht ha hR0 old left right side)) b,
        IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ ha0⟩:=by
  rw [begin_eq_old_start hn ht ha hR0 old] at hb
  let r:=preparedRoot hn ht ha hR0 old left right side
  have HN :number n r=number n (IntegralMixedRoadmapAtomic.root old):=
    IntegralMixedMarkedPreludeCongruence.number_eq _ _ (prepared_candidate hn ht ha hR0 old left right side)
  by_cases hp:b<number n r+8
  · have HC :(IntegralMixedMarkedPrefixCriticalMetadata.header hn ht ha hR0 r b).context=1:=ha0.2
    have HE :IntegralMixedMarkedPrefixCriticalMetadata.header hn ht ha hR0 r b=
        IntegralMixedRoadmapSeedMetadata.stageHeader hn ht ha hR0 r b:=by
      rw [IntegralMixedMarkedPrefixCriticalMetadata.header_actual]
      unfold IntegralMixedRoadmapSeedMetadata.stageHeader IntegralMixedPhysicalMarkedPlan.bank
      rfl
    rw [HE,IntegralMixedRoadmapSeedMetadata.prelude_header hn ht ha hR0 r b hp] at HC
    cases HC
  · have HL :number n (IntegralMixedRoadmapAtomic.root old)+8≤b:=by rw [HN] at hp;omega
    obtain ⟨j,HJ⟩:=Nat.exists_eq_add_of_le HL
    subst b
    exact past_critical_raw_stage hn ht ha hR0 old hv hd left right side hE w hw hr j (by omega) ha0

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

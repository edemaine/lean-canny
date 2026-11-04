/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendWord
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysicalArity
public import LeanCanny.Geometry.IntegralMixedChronologicalLevelPhysicalReadback
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedNativeReadback
/-! # The own sampled proper-append word reads its constructed physical points -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedFrozenFrame
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "oldCs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd e he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd e he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd e he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd e he
local notation "g"=>IntegralMixedRoadmapProperParent.objective hn ht ha hR0 old hv hd
local notation "hg"=>IntegralMixedRoadmapProperParent.objective_free hn ht ha hR0 old hv hd
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old
variable (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "good"=>endpoints_good hn ht ha hR0 old hv hd left right R
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "j"=>start hn ht ha hR0 old
local notation "hj"=>prepared_start_fit hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "newCs"=>parentCommands hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "newX"=>parentState hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good
local notation "startX"=>IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0 r j hj

noncomputable local instance properAppendPhysicalIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  preparedRoot parentCommands parentState IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapAtomic.depth

local notation "q"=>packet D old R.leftSpec R.rightSpec side []
local notation "K"=>List.length (R.orderedFree hk)

local notation "BK"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "T"=>IntegralMixedPhysicalMarkedPlan.tables hn ht ha (radius_binary hR0) false
local notation "SI"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX"=>pair r []
local notation "CAmb"=>IntegralCriticalHistoryTask.Parameters.ambient P c
local notation "AAmb"=>IntegralCriticalHistoryTask.Parameters.ambient P r
local notation "S0"=>IntegralCriticalHistoryTask.Parameters.cap P c+1
local notation "BW0"=>IntegralCriticalHistoryTask.Parameters.width P c
local notation "hQ0"=>IntegralMixedStaticRecordPrefix.cap (Q c) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 c)
local notation "L0"=>IntegralMixedFramedPhysicalIndex.arity
  (List.append (α:=Instruction CAmb BW0)
    (R.result.commands.map (IntegralMixedFramedFixedContinuation.wrap (Q c) hQ0)) oldCs)
local notation "mid0"=>List.length oldCs+R.result.commands.length
local notation "mid"=>IntegralMixedRoadmapProper.midBirth
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
local notation "key"=>IntegralFramedBankQuery.Bank.key BK CTX
open IntegralMixedFramedPhysicalIndex (arity prefixArity enumerate)

private theorem context_eq :IntegralMixedRoadmapAtomic.context q=CTX:=by
  unfold IntegralMixedRoadmapAtomic.context preparedRoot
  rfl

include side in
theorem physical_horizon :(oldCs).length+R.result.commands.length+2+2*K≤S0+1:=by
  have H:=canonical_program_room hn ht ha hR0 old hv hd left right R side
  rw [R.levelCommands_length] at H
  omega

noncomputable def PhysicalReadback (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ):Prop:=
  NativePair.PhysicalReadback hQ0 oldCs R hk g hg side
    (physical_horizon hn ht ha hR0 old hv hd left right R side)
    (canonicalObservation hn ht ha hR0 old hv hd left right R side).arity u pMID pChild
    (fun idx=>(canonicalObservation hn ht ha hR0 old hv hd left right R side).point u idx)

attribute [local irreducible] PhysicalReadback NativePair.PhysicalReadback

private theorem cancel_exact_blocks {a0 a1 a2 a3 a4 a5 a6 a7 :ℕ}
    (HA :a0=a1+a3*(2+2*a7)) (HB :a0=a2+a4*(a5-a6))
    (hc :a3=a4) (hl :a5=a6+2+2*a7):a2=a1:=by
  subst a4
  have HE :a5-a6=2+2*a7:=by omega
  rw [HE] at HB
  omega

theorem prefix_arity_midpoint :prefixArity (BK).parameters T (pair key (List.replicate mid true))=L0:=by
  have HCanon:=R.level_physical_arity hQ0 oldCs hk g hg side
  have HComp :arity (compiledProgram hn ht ha hR0 old hv hd left right R side)=
      arity (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side):=by
    simpa only [compiledObservation,canonicalObservation,IntegralMixedFramedRunObservation.ofCommands] using
      tuple_arity hn ht ha hR0 old hv hd left right R side
  have HA :arity (compiledProgram hn ht ha hR0 old hv hd left right R side)=L0+(2*CAmb+4)*(2+2*K):=
    HComp.trans HCanon
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HT:=full_birth hn ht ha hR0 old hv hd left right R side
  have HB:=prefix_arity_after_mid hn ht ha hR0 old hv hd left right R side
    (finishBirth hn ht ha hR0 old hv hd left right R side) (by omega) (by omega)
  rw [prefix_arity_finish hn ht ha hR0 old hv hd left right R side] at HB
  rw [context_eq hn ht ha hR0 old hv hd left right R side] at HB
  exact cancel_exact_blocks HA HB
    (congrArg (fun a=>2*a+4) (IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e)) HF

private theorem midpoint_canonical_birth :mid=mid0:=by
  have H:=midpoint_birth hn ht ha hR0 old hv hd left right R side
  have HL :(oldCs).length=beginBirth hn ht ha hR0 old:=by
    simpa only [IntegralMixedRoadmapRetainedAppend.beginBirth,beginBirth] using
      IntegralMixedRoadmapRetainedAppend.parent_length hn ht ha hR0 old hv hd e he
  omega

private theorem canonical_resources :
    (P).ambient r=(P).ambient c ∧(P).cap r=(P).cap c ∧(P).width r=(P).width c:=by
  have HC:IntegralMixedAuxiliaryMarkedIntegerSource.candidate r=IntegralMixedAuxiliaryMarkedIntegerSource.candidate c:=
    (prepared_candidate hn ht ha hR0 old R.leftSpec R.rightSpec side).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_candidate hn ht ha hR0 old e).symm
  have HCount:IntegralMixedCausalRecordPlanBits.count r=IntegralMixedCausalRecordPlanBits.count c:=
    (prepared_count hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good).trans
      (IntegralMixedRoadmapRetainedAppend.prepared_count hn ht ha hR0 old hv hd e he).symm
  exact ⟨IntegralMixedMarkedPrefixParameters.ambient hn ht ha hR0 r c HC,
    IntegralMixedMarkedPrefixParameters.cap hn ht ha hR0 r c HC HCount,
    IntegralMixedMarkedPrefixParameters.width hn ht ha hR0 r c HC⟩

private theorem actual_bank_ambient (root :List Bool):(BK).parameters.ambient root=(P).ambient root:=by
  unfold IntegralMixedPhysicalMarkedPlan.bank IntegralMixedAuxiliaryMarkedRecordPlan.bank
  rfl

private theorem physical_root :pairFst key=r:=by
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),pairFst_pair]

theorem padding_dimension :(BK).parameters.ambient (pairFst key)=AAmb:=by
  rw [physical_root hn ht ha hR0 old hv hd left right R side]
  exact actual_bank_ambient hn ht ha hR0 r

theorem physical_dimension :(BK).parameters.ambient (pairFst key)=CAmb:=
  (padding_dimension hn ht ha hR0 old hv hd left right R side).trans
    (canonical_resources hn ht ha hR0 old hv hd left right R side).1

noncomputable def nativeCanonicalPoint (p :Fin (CAmb+1)→ℝ):
    Fin ((BK).parameters.ambient (pairFst key)+1)→ℝ:=
  fun i=>p (Fin.cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old hv hd left right R side)) i)

noncomputable def nativePaddingPoint (p :Fin (AAmb+1)→ℝ):
    Fin ((BK).parameters.ambient (pairFst key)+1)→ℝ:=
  fun i=>p (Fin.cast (congrArg (·+1) (padding_dimension hn ht ha hR0 old hv hd left right R side)) i)

private theorem canonical_arity :(canonicalObservation hn ht ha hR0 old hv hd left right R side).arity=
    L0+(2*CAmb+4)*(2+2*K):=by
  change arity (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)=_
  exact R.level_physical_arity hQ0 oldCs hk g hg side

private theorem canonical_power (b :ℕ):
    UniformIntegralPowerSchedule.physical S0 (2^BW0) b=
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b:=
  congrArg₂ (fun s w=>UniformIntegralPowerSchedule.physical (s+1) (2^w) b)
    (canonical_resources hn ht ha hR0 old hv hd left right R side).2.1.symm
    (canonical_resources hn ht ha hR0 old hv hd left right R side).2.2.symm

private theorem transport_block (raw :ℕ→ℝ) (base span birth start0 start1 count index oldPower newPower :ℕ)
    (v0 v1 :ℝ) (ha :start0=start1) (hp :oldPower=newPower)
    (H :raw (base+span*(birth-start0)+index)^oldPower=if birth<start0+1+count then v0 else v1):
    raw (base+span*(birth-start1)+index)^newPower=if birth<start1+1+count then v0 else v1:=by
  subst start1
  rw [←hp]
  exact H

private theorem readback_local_block (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finishBirth hn ht ha hR0 old hv hd left right R side)
    (i :Fin (CAmb+1)):
    u (L0+(2*CAmb+4)*(b-mid)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=
      if b<mid+1+K then pMID i else pChild i:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  unfold PhysicalReadback NativePair.PhysicalReadback at N
  obtain ⟨A,E,ordinal,hen,HN⟩:=N
  have HC:=midpoint_canonical_birth hn ht ha hR0 old hv hd left right R side
  have HB0 :mid0≤b:=by omega
  have HB1 :b<mid0+2+2*K:=by omega
  have H:=NativePair.NaturalReadback.powered_block (n:=CAmb) (S:=S0) (B:=BW0) (m:=(oldCs).length) («P»:=Q c) hQ0 oldCs R hk g hg _ _ _ side _
    pMID pChild A E HN hen b HB0 HB1 i
  exact transport_block u L0 (2*CAmb+4) b mid0 mid K i.val
    (UniformIntegralPowerSchedule.physical S0 (2^BW0) b)
    (UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b)
    (pMID i) (pChild i) HC.symm
    (canonical_power hn ht ha hR0 old hv hd left right R side b) H

/-- The existing natural witness fixes the entire locally constructed block;
only W's already-proved preservation is used to pass to the sampled tuple. -/
theorem receipt_local_block (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finishBirth hn ht ha hR0 old hv hd left right R side)
    (i :Fin (CAmb+1)):
    W.tuple (L0+(2*CAmb+4)*(b-mid)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=
      if b<mid+1+K then pMID i else pChild i:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HM :b-mid+1≤2+2*K:=by omega
  have HMul:=Nat.mul_le_mul_left (2*CAmb+4) HM
  have HI :L0+(2*CAmb+4)*(b-mid)+i.val<(canonicalObservation hn ht ha hR0 old hv hd left right R side).arity:=by
    rw [canonical_arity hn ht ha hR0 old hv hd left right R side]
    nlinarith [i.isLt]
  rw [W.preserved _ HI]
  exact readback_local_block hn ht ha hR0 old hv hd left right R side u pMID pChild N b hb0 hb1 i

private theorem native_physical_power (root :List Bool) (b :ℕ):
    IntegralMixedFramedCriticalGuardBits.physicalPower (BK).parameters (BK).key (fun _=>b) (pair root [])=
      UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root) b:=by
  unfold IntegralMixedFramedCriticalGuardBits.physicalPower
  rw [IntegralMixedPhysicalFieldEquality.key_root hn ht ha (radius_binary hR0),pairFst_pair]
  unfold IntegralMixedPhysicalMarkedPlan.bank
  rfl

private theorem native_active (b :ℕ) (hb0 :mid≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side):
    IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b:=by
  constructor
  · have H:=native_full_prefix hn ht ha hR0 old hv hd left right R side
    rw [context_eq hn ht ha hR0 old hv hd left right R side] at H
    simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate,H] using hb1
  · have H:=new_header_context hn ht ha hR0 old hv hd left right R side b hb0 hb1
    rw [context_eq hn ht ha hR0 old hv hd left right R side] at H
    simpa only [IntegralMixedFramedCriticalGuardBits.header,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
      IntegralFramedPhysicalCriticalGuardScan.stage,pairFst_pair,pairSnd_pair,List.length_replicate] using H

private theorem geometric_tuple (u :ℕ→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side)
    (i :Fin ((BK).parameters.ambient (pairFst key)+1)):
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b i=
      W.tuple (prefixArity (BK).parameters T (pair key (List.replicate b true))+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b:=by
  have HJ:=IntegralMixedRoadmapSeedResampling.seed_candidates hn ht ha hR0 CTX W.word W.valid W.tuple W.joint
  have HA:=native_active hn ht ha hR0 old hv hd left right R side b hb0 hb1
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt (BK).parameters T
    (IntegralFramedPhysicalCriticalGuardTest.keyDatum (BK).key) (fun _=>i.val)
    IntegralFramedPhysicalCriticalGuardScan.stage (pair CTX (List.replicate b true)) HA
    (by simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using i.isLt)
  have HE:=IntegralMixedPhysicalGuardScan.count_eq hn ht ha (radius_binary hR0) false CTX (List.replicate b true)
  have HC :prefixArity (BK).parameters T (pair key (List.replicate b true))+i.val<(SI).count CTX:=by
    simpa only [IntegralMixedFramedPointEqualityBits.column,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
      pairFst_pair,pairSnd_pair,List.length_replicate] using HL.trans_eq HE
  unfold IntegralMixedPhysicalPointCompanionScan.geometricPoint IntegralMixedPhysicalPointEquality.block
  rw [dite_eq_left HC]
  have HV:=HJ ⟨_,HC⟩
  exact (congrArg (fun v:ℝ=>v^IntegralMixedFramedCriticalGuardBits.physicalPower (BK).parameters
    (BK).key (fun _=>b) CTX) HV).trans (congrArg (fun k=>W.tuple
      (prefixArity (BK).parameters T (pair key (List.replicate b true))+i.val)^k)
      (native_physical_power hn ht ha hR0 r b))

theorem receipt_padding_block (u :ℕ→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :finishBirth hn ht ha hR0 old hv hd left right R side≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side) (i :Fin (AAmb+1)):
    W.tuple (arity (compiledProgram hn ht ha hR0 old hv hd left right R side)+
        (2*AAmb+4)*(b-finishBirth hn ht ha hR0 old hv hd left right R side)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r) b=p0 i:=by
  let k:=(IntegralMixedCanonicalPadding.paddingSelections AAmb
    (seedTailCount hn ht ha hR0 old hv hd left right R side)).length
  have HK :k=seedTailCount hn ht ha hR0 old hv hd left right R side:=
    IntegralMixedCanonicalPadding.paddingSelections_length _ _
  have HF:=full_birth hn ht ha hR0 old hv hd left right R side
  let a :Fin k:=⟨k-1-(b-finishBirth hn ht ha hR0 old hv hd left right R side),by omega⟩
  have HA :k-1-a.val=b-finishBirth hn ht ha hR0 old hv hd left right R side:=by dsimp only [a];omega
  have HB :(compiledProgram hn ht ha hR0 old hv hd left right R side).length+(k-1-a.val)=b:=by
    rw [compiled_program_length hn ht ha hR0 old hv hd left right R side]
    omega
  have H:=W.padding_blocks a i
  change W.tuple (arity (compiledProgram hn ht ha hR0 old hv hd left right R side)+(2*AAmb+4)*(k-1-a.val)+i.val)^
    UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
      ((compiledProgram hn ht ha hR0 old hv hd left right R side).length+(k-1-a.val))=p0 i at H
  rw [HB,HA] at H
  exact H

theorem physical_bank_values (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (idx :Fin ((oldCs).length+R.result.commands.length+1+K+1+K)):
    (canonicalObservation hn ht ha hR0 old hv hd left right R side).point u idx.val=
      IntegralMixedPointCompanion.values pChild
        (Fin.cons (pChild g) (IntegralMixedPointCompanion.values pMID
          (Fin.cons (pMID g) R.result.nextValues) (R.orderedFree hk))) (R.orderedFree hk) idx:=by
  unfold PhysicalReadback NativePair.PhysicalReadback at N
  obtain ⟨A,E,ordinal,hen,HN⟩:=N
  exact HN.bank_values idx

private theorem native_arity_after_mid (b :ℕ) (hb0 :mid≤b)
    (hb1 :b≤fullBirth hn ht ha hR0 old hv hd left right R side):
    prefixArity (BK).parameters T (pair key (List.replicate b true))=L0+(2*CAmb+4)*(b-mid):=by
  have H:=prefix_arity_after_mid hn ht ha hR0 old hv hd left right R side b hb0 hb1
  rw [context_eq hn ht ha hR0 old hv hd left right R side] at H
  rw [prefix_arity_midpoint hn ht ha hR0 old hv hd left right R side] at H
  exact H.trans (congrArg (fun a=>L0+(2*a+4)*(b-mid))
    (IntegralMixedRoadmapRetainedAppend.prepared_dimension hn ht ha hR0 old e).symm)

private theorem native_arity_for_padding (b :ℕ)
    (hb0 :finishBirth hn ht ha hR0 old hv hd left right R side≤b)
    (hb1 :b≤fullBirth hn ht ha hR0 old hv hd left right R side):
    prefixArity (BK).parameters T (pair key (List.replicate b true))=
      arity (compiledProgram hn ht ha hR0 old hv hd left right R side)+
        (2*AAmb+4)*(b-finishBirth hn ht ha hR0 old hv hd left right R side):=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have H:=IntegralMixedFramedPhysicalIndex.prefixArity_critical_interval (BK).parameters T key
    (finishBirth hn ht ha hR0 old hv hd left right R side) b hb0 (by
      intro idx hi0 hi1
      have HC:=new_header_context hn ht ha hR0 old hv hd left right R side idx (by omega) (hi1.trans_le hb1)
      simpa only [context_eq hn ht ha hR0 old hv hd left right R side] using HC)
  have HA:=prefix_arity_finish hn ht ha hR0 old hv hd left right R side
  rw [context_eq hn ht ha hR0 old hv hd left right R side] at HA
  rw [HA] at H
  exact H.trans (congrArg (fun a=>arity (compiledProgram hn ht ha hR0 old hv hd left right R side)+
    (2*a+4)*(b-finishBirth hn ht ha hR0 old hv hd left right R side))
      (padding_dimension hn ht ha hR0 old hv hd left right R side))

/-- The actual own word reads the prescribed MID, CHILD, and seed physical
points, with native dimensions and all physical-column bounds derived here. -/
theorem physical_of_word_receipt (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side):
    IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b=
      if b<IntegralMixedRoadmapAtomic.anchor (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
          (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q then
        nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pMID
      else if b<finishBirth hn ht ha hR0 old hv hd left right R side then
        nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild
      else nativePaddingPoint hn ht ha hR0 old hv hd left right R side p0:=by
  have HCB:=child_anchor hn ht ha hR0 old hv hd left right R side
  funext idx
  simp only [ite_apply]
  rw [geometric_tuple hn ht ha hR0 old hv hd left right R side u p0 W b hb0 hb1 idx]
  by_cases HL :b<finishBirth hn ht ha hR0 old hv hd left right R side
  · let ic:=Fin.cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old hv hd left right R side)) idx
    have H:=receipt_local_block hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b hb0 HL ic
    rw [native_arity_after_mid hn ht ha hR0 old hv hd left right R side b hb0 hb1.le]
    simpa only [ic,Fin.cast,nativeCanonicalPoint,HCB,ite_eq_left HL] using H
  · have HC :¬b<IntegralMixedRoadmapAtomic.anchor
        (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
        (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q:=by
      rw [HCB]
      have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
      omega
    let ia:=Fin.cast (congrArg (·+1) (padding_dimension hn ht ha hR0 old hv hd left right R side)) idx
    have H:=receipt_padding_block hn ht ha hR0 old hv hd left right R side u p0 W b (by omega) hb1 ia
    rw [native_arity_for_padding hn ht ha hR0 old hv hd left right R side b (by omega) hb1.le]
    simpa only [ia,Fin.cast,nativePaddingPoint,ite_eq_right HL,ite_eq_right HC] using H

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendFieldScalar
public import LeanCanny.Encoding.IntegralMixedRoadmapCheckedSeedSelected
/-! # Every critical suffix stage correlates its retained scalar and physical coordinate -/
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

noncomputable local instance properAppendCriticalSuffixIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

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

local notation "anchor"=>IntegralMixedRoadmapAtomic.anchor
  (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
  (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q) q
local notation "sel"=>IntegralMixedPhysicalPointCompanionScan.selected hn ht ha (radius_binary hR0) false CTX
attribute [local irreducible] PhysicalReadback NativePair.PhysicalReadback
  IntegralMixedPhysicalFieldEquality.point IntegralMixedPhysicalPointCompanionScan.retained
  IntegralMixedPhysicalPointCompanionScan.geometricPoint

private theorem suffix_context_eq :IntegralMixedRoadmapAtomic.context q=CTX:=by
  unfold IntegralMixedRoadmapAtomic.context preparedRoot
  rfl

private theorem extend_cast {a0 a1 :ℕ} (h :a0=a1) (p :Fin a1→ℝ) (idx :Fin a0):
    IntegralMixedFramedBankObservation.extend p idx.val=p (Fin.cast h idx):=by
  unfold IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left (idx.isLt.trans_eq h)]
  apply congrArg p
  apply Fin.ext
  rfl

private theorem scalar_local_correlation (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<finishBirth hn ht ha hR0 old hv hd left right R side)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false CTX W.word W.valid b hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b
        ⟨sel b,IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩:=by
  have hValues :∀idx :Fin ((oldCs).length+R.result.commands.length+1+K+1+K),
      (canonicalObservation hn ht ha hR0 old hv hd left right R side).point u idx.val=
        IntegralMixedChronologicalLevelScalarValues.levelValues pMID pChild R.result.nextValues g (R.orderedFree hk) idx:=by
    intro idx
    exact physical_bank_values hn ht ha hR0 old hv hd left right R side u pMID pChild N idx
  have HS:=W.scalar_before_finish hn ht ha hR0 old hv hd left right R side pMID pChild hValues b hb0 hb1
  rw [suffix_context_eq hn ht ha hR0 old hv hd left right R side] at HS
  have HF:=full_birth hn ht ha hR0 old hv hd left right R side
  have HG:=physical_of_word_receipt hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b hb0 (by omega)
  let idx :Fin ((BK).parameters.ambient (pairFst key)+1):=
    ⟨sel b,IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩
  have HC:=extend_cast (congrArg (·+1) (physical_dimension hn ht ha hR0 old hv hd left right R side))
    (if b<anchor then pMID else pChild) idx
  have HE :IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) CTX W.word W.valid b=
      if b<anchor then nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pMID idx
        else nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild idx:=by
    exact HS.trans (by simpa only [ite_apply,nativeCanonicalPoint] using HC)
  have HV :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b idx=
      if b<anchor then nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pMID idx
        else nativeCanonicalPoint hn ht ha hR0 old hv hd left right R side pChild idx:=by
    simpa only [ite_apply,ite_eq_left hb1] using congrFun HG idx
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0) CTX W.word W.valid b hb).trans
    (HE.trans HV.symm)

private theorem suffix_seed_selected (b :ℕ)
    (hb0 :finishBirth hn ht ha hR0 old hv hd left right R side≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side):sel b=0:=by
  have HC0:=pair_checked hn ht ha hR0 old hv hd left right R side []
  have HC :IntegralMixedRoadmapChain.Checked
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.width hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.sourceCap hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 q)
      (IntegralMixedRoadmapAtomic.scalarBudget hn ht ha q) (IntegralMixedRoadmapAtomic.payload q):=by
    rw [dimension_packet,initial_packet,payload_packet]
    simpa only [IntegralMixedRoadmapAtomic.scalarBudget,original_packet] using HC0
  have HP :IntegralMixedRoadmapChain.probe (IntegralMixedRoadmapAtomic.payload q)=
      IntegralMixedRoadmapChain.seedCode (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 q):=by
    rw [payload_packet,dimension_packet]
    unfold payload
    exact IntegralMixedRoadmapChain.append_seed_probe _ _ _ _ _
  have H:=IntegralMixedRoadmapCheckedSeedSelected.selected_after_end hn ht ha hR0 q HC HP b
    (by rw [end_birth_finish hn ht ha hR0 old hv hd left right R side];exact hb0)
    (by rw [native_full_prefix hn ht ha hR0 old hv hd left right R side];exact hb1)
  rw [suffix_context_eq hn ht ha hR0 old hv hd left right R side] at H
  exact H

private theorem scalar_padding_correlation (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :finishBirth hn ht ha hR0 old hv hd left right R side≤b)
    (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false CTX W.word W.valid b hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b
        ⟨sel b,IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩:=by
  have HF:=finish_midpoint hn ht ha hR0 old hv hd left right R side
  have HC:=child_anchor hn ht ha hR0 old hv hd left right R side
  have HM :mid≤b:=by omega
  have HL :¬b<finishBirth hn ht ha hR0 old hv hd left right R side:=by omega
  have HMid :¬b<anchor:=by omega
  have HS:=W.padding_field hn ht ha hR0 old hv hd left right R side b hb0 hb1
  have HG:=physical_of_word_receipt hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b HM hb1
  have HSel:=suffix_seed_selected hn ht ha hR0 old hv hd left right R side b hb0 hb1
  let idx :Fin ((BK).parameters.ambient (pairFst key)+1):=
    ⟨sel b,IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩
  have HIndex :Fin.cast (congrArg (·+1) (padding_dimension hn ht ha hR0 old hv hd left right R side)) idx=
      (0:Fin (AAmb+1)):=by
    apply Fin.ext
    simpa only [idx,Fin.cast,Fin.val_zero] using HSel
  have HV :IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b idx=p0 0:=by
    have H:=congrFun HG idx
    rw [ite_eq_right HMid,ite_eq_right HL] at H
    exact H.trans (by unfold nativePaddingPoint;rw [HIndex])
  exact (IntegralMixedPhysicalFieldEquality.retained_point hn ht ha (radius_binary hR0) CTX W.word W.valid b hb).trans
    (HS.trans HV.symm)

/-- Every active creating stage in the actual MID/CHILD/seed suffix has the
native retained-selected physical correlation, from the SAME W and N only. -/
theorem suffix_critical (u :ℕ→ℝ) (pMID pChild :Fin (CAmb+1)→ℝ) (p0 :Fin (AAmb+1)→ℝ)
    (N :PhysicalReadback hn ht ha hR0 old hv hd left right R side u pMID pChild)
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side u p0)
    (b :ℕ) (hb0 :mid≤b) (hb1 :b<fullBirth hn ht ha hR0 old hv hd left right R side)
    (hb :IntegralMixedPhysicalPointCompanionScan.Active hn ht ha (radius_binary hR0) false CTX b):
    IntegralMixedPhysicalPointCompanionScan.retained hn ht ha (radius_binary hR0) false CTX W.word W.valid b hb=
      IntegralMixedPhysicalPointCompanionScan.geometricPoint hn ht ha (radius_binary hR0) false CTX W.word W.valid b
        ⟨sel b,IntegralMixedPhysicalPointCompanionScan.selected_lt hn ht ha (radius_binary hR0) false _ _ hb⟩:=by
  by_cases HL :b<finishBirth hn ht ha hR0 old hv hd left right R side
  · exact scalar_local_correlation hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b hb0 HL hb
  · exact scalar_padding_correlation hn ht ha hR0 old hv hd left right R side u pMID pChild p0 N W b (by omega) hb1 hb

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

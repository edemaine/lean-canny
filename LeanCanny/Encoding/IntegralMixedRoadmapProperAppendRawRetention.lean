/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPhysical
public import LeanCanny.Encoding.IntegralMixedMarkedJointNatural
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastValues
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalPersistence
/-! # A sampled proper append retains the verifier's entire old natural tuple -/
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

noncomputable local instance properAppendRawRetentionIndexFintype :Fintype (Index (Fin 0) oldCs):=indexFintype (Fin 0) oldCs

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

local notation "CObs"=>canonicalObservation hn ht ha hR0 old hv hd left right R side
local notation "FObs"=>IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r
local notation "localCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side

theorem canonical_arity_le_full :(CObs).arity≤(FObs).arity:=by
  have HC:=tuple_arity hn ht ha hR0 old hv hd left right R side
  have HC' :arity localCs=(CObs).arity:=by
    simpa only [compiledObservation,IntegralMixedFramedRunObservation.ofCommands] using HC
  have HF :(FObs).arity=arity ((PLAN).rules r):=rfl
  rw [HF,←HC',full_commands hn ht ha hR0 old hv hd left right R side]
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem old_arity_le_canonical :arity oldCs≤(CObs).arity:=by
  change arity oldCs≤arity (canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side)
  unfold canonicalCompiledProgram
  exact IntegralMixedFramedPhysicalPersistence.arity_le_append _ _

theorem WordReceipt.natural_local {z :ℕ→ℝ} {p0 :Fin (AAmb+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (idx :ℕ) (hidx :idx<(CObs).arity):
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid idx=z idx:=
  (IntegralMixedMarkedJointNatural.natural_eq hn ht ha hR0 r W.word W.valid W.tuple W.joint idx
    (hidx.trans_le (canonical_arity_le_full hn ht ha hR0 old hv hd left right R side))).trans
      (W.preserved idx hidx)

theorem WordReceipt.old_raw {z :ℕ→ℝ} {p0 :Fin (AAmb+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (hOld :∀idx,idx<arity oldCs→z idx=oldNatural hn ht ha hR0 old hv idx):
    ∀idx,idx<arity newCs→
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 r W.word W.valid idx=
        oldNatural hn ht ha hR0 old hv idx:=by
  have HA:=(parent_layout hn ht ha hR0 old hv hd R.leftSpec R.rightSpec side good).2.1
  intro idx hidx
  have HI :idx<arity oldCs:=hidx.trans_eq HA
  exact (W.natural_local hn ht ha hR0 old hv hd left right R side idx
    (HI.trans_le (old_arity_le_canonical hn ht ha hR0 old hv hd left right R side))).trans (hOld idx HI)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

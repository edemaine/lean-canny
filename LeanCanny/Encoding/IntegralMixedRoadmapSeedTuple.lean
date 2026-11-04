/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
public import LeanCanny.Encoding.IntegralMixedMarkedReservedCutView
/-! # The concrete seed root retains the old prelude and realizes every block -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem observation_commands {n S B :ℕ} {Q :SpatialSource n}
    (x :State Q S B 0 (Fin 0)) (cs ds :List (Instruction n B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds) :
    ofCommands x cs hc=ofCommands x ds hd:=by cases he;rfl

variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank
  IntegralMixedMarkedReservedParent.bank IntegralMixedAuxiliaryMarkedRecordPlan.parameters
  IntegralMixedExceptionalBounds.auxiliaryCap

theorem prepared_dimension (old :List Bool) :
    (P).ambient (preparedRoot hn ht ha hR0 old)=IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old:=by
  have HA:(P).ambient=(IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha).ambient:=rfl
  rw [HA,IntegralMixedRoadmapAtomic.dimension_eq]
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.parameters
  change number n (preparedRoot hn ht ha hR0 old)+3=n (IntegralMixedRoadmapAtomic.original old)+3
  simp only [preparedRoot,number,IntegralMixedAuxiliaryMarkedIntegerSource.original,
    IntegralMixedAuxiliaryMarkedIntegerSource.candidate,IntegralMixedRoadmapAtomic.root,
    candidate_packet,pairFst_pair,IntegralMixedRoadmapAtomic.original]

theorem prepared_records (old :List Bool) :
    IntegralMixedCausalRecordPlanBits.records (preparedRoot hn ht ha hR0 old)=
      WordList.encode (IntegralMixedRoadmapChain.seedCodes ((P).ambient (preparedRoot hn ht ha hR0 old))++
        List.replicate (IntegralMixedRoadmapChain.paddingCount ((P).ambient (preparedRoot hn ht ha hR0 old))
          (payload ((P).ambient (preparedRoot hn ht ha hR0 old)))+1)
          (IntegralMixedRoadmapChain.seedCode ((P).ambient (preparedRoot hn ht ha hR0 old)))):=by
  rw [prepared_dimension]
  simpa only [IntegralMixedCausalRecordPlanBits.records,preparedRoot,IntegralMixedRoadmapAtomic.root,
    candidate_packet,payload_packet,pairFst_pair,pairSnd_pair] using
      raw_exact (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)

noncomputable def seedOlder (old :List Bool):=
  IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 (preparedRoot hn ht ha hR0 old) 0 (Nat.zero_le _)
noncomputable def seedTail (old :List Bool):=
  IntegralMixedRoadmapChain.paddingCount ((P).ambient (preparedRoot hn ht ha hR0 old))
    (payload ((P).ambient (preparedRoot hn ht ha hR0 old)))+1
noncomputable def seedSelections (old :List Bool):=
  IntegralMixedChronologicalSeedProgram.selections ((P).ambient (preparedRoot hn ht ha hR0 old))
    (seedOlder hn ht ha hR0 old).length (seedTail hn ht ha hR0 old)

attribute [local irreducible] seedOlder seedTail seedSelections preparedRoot
  IntegralMixedMarkedRecordContinuation.oldCommands IntegralMixedMarkedConstructedPrefix.state
  IntegralMixedMarkedRecordContinuation.start IntegralMixedFramedRunObservation.ofCommands

theorem seed_length (old :List Bool) :
    (seedSelections hn ht ha hR0 old).length=
      IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old):=by
  have HC:=congrArg WordListRecords.count (prepared_records hn ht ha hR0 old)
  rw [WordListRecords.count_encode] at HC
  simp only [List.length_append,IntegralMixedRoadmapChain.seedCodes_length,List.length_replicate] at HC
  rw [seedSelections,IntegralMixedChronologicalSeedProgram.selections_length]
  unfold seedTail
  unfold IntegralMixedCausalRecordPlanBits.count
  omega

theorem seed_older_length (old :List Bool) :
    (seedOlder hn ht ha hR0 old).length=number n (preparedRoot hn ht ha hR0 old)+8:=by
  unfold seedOlder
  exact (IntegralMixedMarkedRecordContinuation.oldCommands_length hn ht ha hR0 _ 0 (Nat.zero_le _)).trans
    (Nat.add_zero _)

theorem seed_room (old :List Bool) :
    (seedOlder hn ht ha hR0 old).length+(seedSelections hn ht ha hR0 old).length≤
      (P).cap (preparedRoot hn ht ha hR0 old)+1+1:=by
  have HL:=seed_older_length hn ht ha hR0 old
  have HS:=seed_length hn ht ha hR0 old
  have HB:=(IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0
    (preparedRoot hn ht ha hR0 old) _ (le_refl _)).trans (Nat.le_succ _)
  omega

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling

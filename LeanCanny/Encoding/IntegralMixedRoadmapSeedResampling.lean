/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedResamplingLayout
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedObservation
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixTransfer
public import LeanCanny.Geometry.IntegralMixedChronologicalSeedProgram
public import LeanCanny.Geometry.IntegralMixedPointCompanionDecoded
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumns
/-! # Concrete depth-zero resampling starts from the old actual physical tuple

The new root has the same candidate and record count. Its integer prelude
is read from the old full word, before constructing any new critical block.
-/
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
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters IntegralMixedExceptionalBounds.auxiliaryCap

noncomputable def preparedRoot (old :List Bool):=
  IntegralMixedRoadmapAtomic.root (packet (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) old [])

theorem prepared_count (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    IntegralMixedCausalRecordPlanBits.count (IntegralMixedRoadmapAtomic.root old)=
      IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old):=by
  simp only [IntegralMixedCausalRecordPlanBits.count,IntegralMixedCausalRecordPlanBits.records,
    preparedRoot,IntegralMixedRoadmapAtomic.root,candidate_packet,payload_packet,pairFst_pair,pairSnd_pair]
  rw [IntegralMixedRoadmapAtomic.raw_count hn ht ha hR0 old hv,raw_count]

theorem old_full_valid (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context (IntegralMixedRoadmapAtomic.root old))
      (IntegralMixedRoadmapAtomic.word old):=by
  have HE :IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false=
      IntegralMixedMarkedReservedParent.input hn ht ha hR0:=by
    unfold IntegralMixedPhysicalMarkedTest.input IntegralMixedPhysicalMarkedPlan.bank
      IntegralMixedMarkedReservedParent.input IntegralMixedMarkedReservedParent.bank
    rfl
  have HV:=IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv
  rw [HE] at HV
  exact HV

noncomputable def oldTuple (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :ℕ→ℝ:=
  IntegralMixedMarkedPrefixTransfer.tuple hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (IntegralMixedRoadmapAtomic.word old)
    (old_full_valid hn ht ha hR0 old hv)

theorem prepared_prelude_roots (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0
      (preparedRoot hn ht ha hR0 old) 0 (Nat.zero_le _)).Roots (oldTuple hn ht ha hR0 old hv):=by
  have HR:=IntegralMixedMarkedPrefixTransfer.base_roots hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (IntegralMixedRoadmapAtomic.word old)
    (old_full_valid hn ht ha hR0 old hv) 0 (Nat.zero_le _)
  have HE:=IntegralMixedMarkedPrefixObservation.eq hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (preparedRoot hn ht ha hR0 old)
    (by simp only [IntegralMixedAuxiliaryMarkedIntegerSource.candidate,preparedRoot,
      IntegralMixedRoadmapAtomic.root,candidate_packet,pairFst_pair])
    (prepared_count hn ht ha hR0 old hv) 0 (Nat.zero_le _) (by intro i hi;omega)
  exact (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots
    (oldTuple hn ht ha hR0 old hv)) HE).mp HR

attribute [local irreducible] IntegralMixedMarkedRecordContinuation.oldCommands
  IntegralMixedMarkedRecordContinuation.records_before

theorem prelude_observation (root :List Bool) :
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root 0 (Nat.zero_le _)=
      ofCommands (initial P D root)
        (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root 0 (Nat.zero_le _))
        (by rw [IntegralMixedMarkedRecordContinuation.oldCommands_length]
            exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)) :=by
  have HE:=IntegralMixedMarkedConstructedPrefix.compiled_commands hn ht ha hR0 root 0 (Nat.zero_le _) []
    (by simp only [List.length_nil,Nat.add_zero];omega) (by intro i hi;simp only [List.length_nil] at hi;omega)
    [] (by simp only [List.length_nil,Nat.add_zero]
           rw [IntegralMixedMarkedRecordContinuation.oldCommands_length]
           exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 root _ (by omega)).trans (Nat.le_succ _)) rfl
  simp only [List.length_nil,Nat.add_zero] at HE
  exact observation_commands (initial P D root) _ _ _ _ HE

noncomputable def preludeTuple (root :List Bool) (u :ℕ→ℝ) :
    Index (Fin 0) (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root 0 (Nat.zero_le _))→ℝ:=
  fun i=>u (enumerate (IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 root 0 (Nat.zero_le _)) i).val

attribute [local irreducible] IntegralMixedMarkedConstructedPrefix.state
  IntegralMixedMarkedRecordContinuation.start
  preparedRoot oldTuple preludeTuple IntegralMixedFramedRunObservation.ofCommands

theorem start_roots (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) :
    ∀i,((IntegralMixedMarkedConstructedPrefix.state hn ht ha hR0
      (preparedRoot hn ht ha hR0 old) 0 (Nat.zero_le _)).sampler.rows i).eval₂ (Int.castRingHom ℝ)
        (preludeTuple hn ht ha hR0 (preparedRoot hn ht ha hR0 old) (oldTuple hn ht ha hR0 old hv))=0:=by
  have HZ:=prepared_prelude_roots hn ht ha hR0 old hv
  have HE:=prelude_observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old)
  have HR:=(IntegralMixedFramedRunObservation.roots_actual (initial P D (preparedRoot hn ht ha hR0 old)) _ _
    (oldTuple hn ht ha hR0 old hv)).mp
      ((congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots
        (oldTuple hn ht ha hR0 old hv)) HE).mp HZ)
  unfold IntegralMixedMarkedConstructedPrefix.state IntegralMixedMarkedRecordContinuation.start
    IntegralMixedCausalUnitContinuation.start preludeTuple
  unfold IntegralMixedMarkedRecordContinuation.oldCommands at HR ⊢
  exact HR

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling

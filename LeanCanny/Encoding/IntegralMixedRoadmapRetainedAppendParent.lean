/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPrefix
public import LeanCanny.Encoding.IntegralMixedMarkedConstructedPrefix
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumns
/-! # The actual appended parent retains the old full natural tuple

Its roots and interpretation are constructed from the old accepted word and
literal prefix congruence. No parent realization or hom is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r

theorem prefix_fit (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    start hn ht ha hR0 old≤IntegralMixedCausalRecordPlanBits.count (preparedRoot hn ht ha hR0 old producer):=
  (start_fit hn ht ha hR0 old hv).trans_eq (prepared_count hn ht ha hR0 old hv hd producer he).symm

noncomputable def parentCommands (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):=
  IntegralMixedMarkedRecordContinuation.oldCommands hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer)
    (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd producer he)

theorem parent_commands (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    paddedPast (defaultInstruction P D (preparedRoot hn ht ha hR0 old producer))
      ((D).rules (preparedRoot hn ht ha hR0 old producer))
      (number n (preparedRoot hn ht ha hR0 old producer)+8+start hn ht ha hR0 old)=
      parentCommands hn ht ha hR0 old hv hd producer he:=by
  let r:=preparedRoot hn ht ha hR0 old producer
  let j:=start hn ht ha hR0 old
  have hj:=prefix_fit hn ht ha hR0 old hv hd producer he
  have H:=IntegralMixedMarkedConstructedPrefix.compiled_commands hn ht ha hR0 r j hj []
    (by simpa only [List.length_nil,Nat.add_zero] using hj) (by intro i hi;simp at hi) []
    (by
      rw [List.length_nil,Nat.add_zero,IntegralMixedMarkedRecordContinuation.oldCommands_length]
      exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 r _
        (by dsimp only [r,j];omega)).trans (Nat.le_succ _)) rfl
  simpa only [List.length_nil,Nat.add_zero,List.map_nil,List.nil_append,parentCommands,r,j] using H

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedAuxiliaryMarkedRecordPlan.parameters preparedRoot start parentCommands

theorem old_full_valid (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old):
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

noncomputable def oldNatural (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old):ℕ→ℝ:=
  IntegralMixedMarkedPrefixTransfer.tuple hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
    (IntegralMixedRoadmapAtomic.word old) (old_full_valid hn ht ha hR0 old hv)

theorem parent_natural_roots (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer)
      (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd producer he)).Roots
        (oldNatural hn ht ha hR0 old hv):=by
  have H:=IntegralMixedMarkedPrefixTransfer.base_roots hn ht ha hR0 (IntegralMixedRoadmapAtomic.root old)
    (IntegralMixedRoadmapAtomic.word old) (old_full_valid hn ht ha hR0 old hv)
    (start hn ht ha hR0 old) (start_fit hn ht ha hR0 old hv)
  exact (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots (oldNatural hn ht ha hR0 old hv))
    (prefix_observation hn ht ha hR0 old hv hd producer he _ (Nat.le_refl _))).mpr H

private theorem observation_commands {a S B :ℕ} {V :SpatialSource a}
    (x :State V S B 0 (Fin 0)) (cs ds :List (Instruction a B))
    (hc :cs.length≤S+1) (hd :ds.length≤S+1) (he :cs=ds):
    IntegralMixedFramedRunObservation.ofCommands x cs hc=
      IntegralMixedFramedRunObservation.ofCommands x ds hd:=by cases he;rfl

theorem parent_observation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer)
      (start hn ht ha hR0 old) (prefix_fit hn ht ha hR0 old hv hd producer he)=
    IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot hn ht ha hR0 old producer))
      (parentCommands hn ht ha hR0 old hv hd producer he)
      (by
        rw [parentCommands,IntegralMixedMarkedRecordContinuation.oldCommands_length]
        exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 _ _
          (by have HH:=prefix_fit hn ht ha hR0 old hv hd producer he;omega)).trans (Nat.le_succ _)):=
  observation_commands _ _ _ _ _ (parent_commands hn ht ha hR0 old hv hd producer he)

theorem parent_room (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    (parentCommands hn ht ha hR0 old hv hd producer he).length≤(P).cap (preparedRoot hn ht ha hR0 old producer)+1+1:=by
  rw [parentCommands,IntegralMixedMarkedRecordContinuation.oldCommands_length]
  exact (IntegralMixedMarkedRecordContinuation.full_bound hn ht ha hR0 _ _
    (by have HH:=prefix_fit hn ht ha hR0 old hv hd producer he;omega)).trans (Nat.le_succ _)

noncomputable def parentTuple (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    Index (Fin 0) (parentCommands hn ht ha hR0 old hv hd producer he)→ℝ:=
  fun i=>oldNatural hn ht ha hR0 old hv (enumerate (parentCommands hn ht ha hR0 old hv hd producer he) i).val

attribute [local semireducible] IntegralMixedAuxiliaryMarkedRecordPlan.parameters
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedFramedRawHeight.rootCeiling IntegralMixedFramedNormalizationBits.requiredModulus
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedExceptionalBounds.auxiliaryCap

noncomputable def parentState (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):=
  reframe (run (initial P D (preparedRoot hn ht ha hR0 old producer))
    (parentCommands hn ht ha hR0 old hv hd producer he) (parent_room hn ht ha hR0 old hv hd producer he))
      (Q (preparedRoot hn ht ha hR0 old producer)) (IntegralMixedStaticRecordPrefix.cap
        (Q (preparedRoot hn ht ha hR0 old producer))
        (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 (preparedRoot hn ht ha hR0 old producer)))

theorem parent_roots (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    ∀i,((parentState hn ht ha hR0 old hv hd producer he).sampler.rows i).eval₂
      (Int.castRingHom ℝ) (parentTuple hn ht ha hR0 old hv hd producer he)=0:=by
  have HR:=parent_natural_roots hn ht ha hR0 old hv hd producer he
  have HO:=parent_observation hn ht ha hR0 old hv hd producer he
  have HT : (IntegralMixedFramedRunObservation.ofCommands (initial P D (preparedRoot hn ht ha hR0 old producer))
      (parentCommands hn ht ha hR0 old hv hd producer he) (parent_room hn ht ha hR0 old hv hd producer he)).Roots
        (oldNatural hn ht ha hR0 old hv):=
    (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots (oldNatural hn ht ha hR0 old hv)) HO).mp HR
  exact (IntegralMixedFramedRunObservation.roots_actual _ _ _ _).mp HT

theorem parent_interpretation (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (producer :ℕ) (he :producer<IntegralMixedRoadmapAtomic.endBirth
      (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old):
    ∃φ :(parentState hn ht ha hR0 old hv hd producer he).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((parentState hn ht ha hR0 old hv hd producer he).sampler.scalarPrefix.basis.generator i)=
        parentTuple hn ht ha hR0 old hv hd producer he ((parentState hn ht ha hR0 old hv hd producer he).sampler.scalar i)^
          UniformIntegralPowerSchedule.weights ((P).cap (preparedRoot hn ht ha hR0 old producer)+1)
            (2^(P).width (preparedRoot hn ht ha hR0 old producer))
            (parentCommands hn ht ha hR0 old hv hd producer he).length i) ∧
      ∀i,φ ((parentState hn ht ha hR0 old hv hd producer he).bank.numerator i)/
        ((parentState hn ht ha hR0 old hv hd producer he).bank.denominator i:ℝ)=
        IntegralMixedFullBankPoint.point (parentState hn ht ha hR0 old hv hd producer he)
          (parentTuple hn ht ha hR0 old hv hd producer he) i:=by
  have HZ:=parent_roots hn ht ha hR0 old hv hd producer he
  unfold parentState at HZ ⊢
  exact IntegralMixedFramedFixedContinuation.before_interprets _ _ _ _ _ _ HZ

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

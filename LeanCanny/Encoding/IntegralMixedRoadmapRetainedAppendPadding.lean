/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendTuple
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPlan
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingPhysicalObservation
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
/-! # Actual seed padding preserves the entire retained-append physical tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "Q" r=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (e :ℕ) (he :e<IntegralMixedRoadmapAtomic.endBirth
    (IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old) (IntegralMixedRoadmapAtomic.initial hn ht ha hR0 old) old)
local notation "r"=>preparedRoot hn ht ha hR0 old e
local notation "older"=>parentCommands hn ht ha hR0 old hv hd e he
local notation "js"=>midpointSelections hn ht ha hR0 old hv hd e he
local notation "cs"=>childSelections hn ht ha hR0 old hv hd e he
local notation "localCs"=>localInstructions hn ht ha hR0 old hv hd e he
local notation "tailCount"=>seedTailCount hn ht ha hR0 old e
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap (Q r) (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)

theorem compiled_program_eq :compiledProgram hn ht ha hR0 old hv hd e he=localCs:=by
  simp only [compiledProgram,localProgram,localInstructions,childInstructions,childCommands,
    midpointPast,midpointInstructions,List.map_append]
  convert List.append_assoc _ _ _ using 1; rfl

theorem local_length :(localCs).length=(older).length+(js).length+(cs).length:=by
  simp only [localInstructions,childInstructions,List.length_append,List.length_map,childCommands,
    IntegralMixedPointCompanion.commands_length,midpoint_past_birth]
  omega

theorem local_arity :arity localCs=arity older+(2*(P).ambient r+4)*(js).length+
    (2*(P).ambient r+4)*(cs).length:=by
  have H:=IntegralMixedFramedFixedContinuation.companion_arity hQ
    (midpointPast hn ht ha hR0 old hv hd e he)
    (childDescriptor hn ht ha hR0 old hv hd e he).frame.frozen (fun _=>false)
    (fun i=>.single ((childDescriptor hn ht ha hR0 old hv hd e he).atom i))
    (childObjective hn ht ha hR0 old hv hd e he) cs
  simp only [midpoint_arity] at H
  convert H using 1 <;> rfl

noncomputable def physicalSeedInstruction :Instruction ((P).ambient r) ((P).width r):=
  IntegralMixedCanonicalPaddingSeed.instruction (Q r) hQ

theorem tail_instruction_eq :tailInstruction hn ht ha hR0 r=
    physicalSeedInstruction hn ht ha hR0 old e:=rfl

theorem full_local_commands :(D).rules r=
    List.replicate tailCount (physicalSeedInstruction hn ht ha hR0 old e)++localCs:=by
  rw [full_commands hn ht ha hR0 old hv hd e he,compiled_program_eq,
    tail_instruction_eq hn ht ha hR0 old e]

theorem full_local_room :(List.replicate tailCount (physicalSeedInstruction hn ht ha hR0 old e)++
    localCs).length≤(P).cap r+1+1:=by
  rw [←full_local_commands hn ht ha hR0 old hv hd e he]
  exact IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 r

noncomputable def localObservation:=IntegralMixedFramedRunObservation.ofCommands (initial P D r)
  localCs (local_room hn ht ha hR0 old hv hd e he)

private theorem observation_congr {dim S B :ℕ} {baseSource :SpatialSource dim}
    (x :State baseSource S B 0 (Fin 0)) (as bs :List (Instruction dim B))
    (ha :as.length≤S+1) (hb :bs.length≤S+1) (h :as=bs):
    IntegralMixedFramedRunObservation.ofCommands x as ha=
      IntegralMixedFramedRunObservation.ofCommands x bs hb:=by
  cases h
  rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  preparedRoot localInstructions

theorem padding_observation_eq :IntegralMixedFramedRunObservation.ofCommands (initial P D r)
    (List.replicate tailCount (physicalSeedInstruction hn ht ha hR0 old e)++localCs)
    (full_local_room hn ht ha hR0 old hv hd e he)=
      IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r:=by
  unfold IntegralMixedMarkedPrefixFieldReadback.fullObservation
  exact observation_congr _ _ _ _ _ (full_local_commands hn ht ha hR0 old hv hd e he).symm

attribute [local irreducible] localObservation IntegralMixedFramedRunObservation.ofCommands
  IntegralMixedMarkedPrefixFieldReadback.fullObservation

theorem pad_local_tuple (z :ℕ→ℝ)
    (hz :(localObservation hn ht ha hR0 old hv hd e he).Roots z)
    (p0 :Fin ((P).ambient r+1)→ℝ)
    (hp0 :(FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree).eval₂
      (Int.castRingHom ℝ) p0=0)
    (hg0 :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p0=0):
    ∃u :ℕ→ℝ,(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).Roots u ∧
      (∀i,i<arity localCs→u i=z i) ∧
      (∀j :Fin (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length,∀i,
        u (arity localCs+(2*(P).ambient r+4)*((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length-1-j.val)+i.val)^
          UniformIntegralPowerSchedule.physical ((P).cap r+1) (2^(P).width r)
            ((localCs).length+((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length-1-j.val))=p0 i) ∧
      ∀i :Fin ((localCs).length+(IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount).length),
        (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r).point u i.val=
          IntegralMixedPointCompanion.values p0
            (fun j=>(localObservation hn ht ha hR0 old hv hd e he).point z j.val)
            (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount) i:=by
  have HD :(Q r).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  have HZ:=hz
  unfold localObservation at HZ
  have HRoom:=full_local_room hn ht ha hR0 old hv hd e he
  unfold physicalSeedInstruction at HRoom
  have H:=@IntegralMixedCanonicalPadding.run_physical_observation
    ((P).ambient r) ((P).cap r+1) ((P).width r) _ (initial P D r) localCs
    (local_room hn ht ha hR0 old hv hd e he) (Q r) hQ
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) _ HD
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r) z HZ p0 hp0 hg0 tailCount HRoom
  have HE:=padding_observation_eq hn ht ha hR0 old hv hd e he
  unfold physicalSeedInstruction at HE
  simpa only [HE,localObservation] using H

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

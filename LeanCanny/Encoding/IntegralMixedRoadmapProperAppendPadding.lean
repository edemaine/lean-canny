/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendTuple
public import LeanCanny.Geometry.IntegralMixedCanonicalPaddingPhysicalObservation
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
/-! # Actual proper-append seed padding retains every constructed raw column -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "PLAN"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "e"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "c"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old e
local notation "newCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "oldCs"=>canonicalCompiledProgram hn ht ha hR0 old hv hd left right R side
open IntegralMixedFramedPhysicalIndex (arity)
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
local notation "localCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "tailCount"=>seedTailCount hn ht ha hR0 old hv hd left right R side
local notation "hQ"=>IntegralMixedStaticRecordPrefix.cap (Q r)
  (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r)

noncomputable def physicalSeedInstruction :Instruction ((P).ambient r) ((P).width r):=
  IntegralMixedCanonicalPaddingSeed.instruction (Q r) hQ

theorem physical_tail_instruction_eq :tailInstruction hn ht ha hR0 r=
    physicalSeedInstruction hn ht ha hR0 old hv hd left right R side:=rfl

theorem full_local_commands :(PLAN).rules r=
    List.replicate tailCount (physicalSeedInstruction hn ht ha hR0 old hv hd left right R side)++localCs:=by
  rw [full_commands hn ht ha hR0 old hv hd left right R side,
    physical_tail_instruction_eq hn ht ha hR0 old hv hd left right R side]

theorem full_local_room :(List.replicate tailCount
    (physicalSeedInstruction hn ht ha hR0 old hv hd left right R side)++localCs).length≤(P).cap r+1+1:=by
  rw [←full_local_commands hn ht ha hR0 old hv hd left right R side]
  exact IntegralMixedMarkedPrefixFieldReadback.room hn ht ha hR0 r

private theorem observation_congr {dim S B :ℕ} {baseSource :SpatialSource dim}
    (x :State baseSource S B 0 (Fin 0)) (as bs :List (Instruction dim B))
    (ha :as.length≤S+1) (hb :bs.length≤S+1) (hcs :as=bs):
    IntegralMixedFramedRunObservation.ofCommands x as ha=
      IntegralMixedFramedRunObservation.ofCommands x bs hb:=by
  cases hcs
  rfl

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  preparedRoot compiledProgram

theorem padding_observation_eq :IntegralMixedFramedRunObservation.ofCommands (initial P PLAN r)
    (List.replicate tailCount (physicalSeedInstruction hn ht ha hR0 old hv hd left right R side)++localCs)
    (full_local_room hn ht ha hR0 old hv hd left right R side)=
      IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 r:=by
  unfold IntegralMixedMarkedPrefixFieldReadback.fullObservation
  exact observation_congr _ _ _ _ _ (full_local_commands hn ht ha hR0 old hv hd left right R side).symm

attribute [local irreducible] compiledObservation canonicalObservation IntegralMixedFramedRunObservation.ofCommands
  IntegralMixedMarkedPrefixFieldReadback.fullObservation

theorem pad_local_tuple (z :ℕ→ℝ)
    (hz :(canonicalObservation hn ht ha hR0 old hv hd left right R side).Roots z)
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
            (fun j=>(canonicalObservation hn ht ha hR0 old hv hd left right R side).point z j.val)
            (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient r) tailCount) i:=by
  have HD :(Q r).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  have HZ:=tuple_roots hn ht ha hR0 old hv hd left right R side z hz
  unfold compiledObservation at HZ
  have HRoom:=full_local_room hn ht ha hR0 old hv hd left right R side
  unfold physicalSeedInstruction at HRoom
  have H:=@IntegralMixedCanonicalPadding.run_physical_observation
    ((P).ambient r) ((P).cap r+1) ((P).width r) _ (initial P PLAN r) localCs
    (compiled_program_room hn ht ha hR0 old hv hd left right R side) (Q r) hQ
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) _ HD
    (IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r) z HZ p0 hp0 hg0 tailCount HRoom
  have HE:=padding_observation_eq hn ht ha hR0 old hv hd left right R side
  unfold physicalSeedInstruction at HE
  have HObs:=compiled_observation_eq hn ht ha hR0 old hv hd left right R side
  unfold compiledObservation at HObs
  simpa only [HE,HObs] using H

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

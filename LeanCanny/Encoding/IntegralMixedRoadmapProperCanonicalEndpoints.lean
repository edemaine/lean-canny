/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendOwnPoint
public import LeanCanny.Geometry.IntegralMixedChronologicalGuardedPair
/-! # An accepted old word constructs its own guarded optional endpoint pair -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperParent
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalFrame
open IntegralMixedChronologicalEndpoint IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedFrozenFrame IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "E"=>IntegralMixedRoadmapAtomic.ownBirth hn ht ha hR0 old
local notation "he"=>IntegralMixedRoadmapRetainedAppend.own_endpoint_fit hn ht ha hR0 old
local notation "r"=>IntegralMixedRoadmapRetainedAppend.preparedRoot hn ht ha hR0 old E
local notation "cs"=>IntegralMixedRoadmapRetainedAppend.parentCommands hn ht ha hR0 old hv hd E he
local notation "x"=>IntegralMixedRoadmapRetainedAppend.parentState hn ht ha hR0 old hv hd E he
local notation "d"=>IntegralMixedRoadmapRetainedAppend.parentDescriptor hn ht ha hR0 old hv hd E he
local notation "hk"=>IntegralMixedRoadmapRetainedAppend.parent_descriptor_fit hn ht ha hR0 old hv hd E he
local notation "z"=>IntegralMixedRoadmapRetainedAppend.parentTuple hn ht ha hR0 old hv hd E he
local notation "V"=>IntegralMixedRoadmapRetainedAppend.parentValues hn ht ha hR0 old hv hd E he
local notation "Q"=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) r
local notation "hc"=>IntegralMixedMarkedPrefixRecords.source_cap hn ht ha hR0 r
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedRoadmapAtomic.dimension
  IntegralMixedRoadmapAtomic.initial IntegralMixedRoadmapRetainedAppend.preparedRoot
  IntegralMixedRoadmapRetainedAppend.parentCommands IntegralMixedRoadmapRetainedAppend.parentState
  IntegralMixedRoadmapRetainedAppend.parentDescriptor IntegralMixedRoadmapRetainedAppend.parentTuple
  IntegralMixedRoadmapRetainedAppend.parentValues IntegralMixedExceptionalBounds.auxiliaryCap
  IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedFramedRawHeight.rootCeiling
  IntegralMixedFramedNormalizationBits.requiredModulus

noncomputable local instance :Fintype (Index (Fin 0) cs):=indexFintype (Fin 0) cs

noncomputable def hom :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ:=
  Classical.choose (IntegralMixedRoadmapRetainedAppend.parent_interpretation hn ht ha hR0 old hv hd E he)

theorem hom_generators :∀i,hom hn ht ha hR0 old hv hd ((x).sampler.scalarPrefix.basis.generator i)=
    z ((x).sampler.scalar i)^UniformIntegralPowerSchedule.weights ((P).cap r+1) (2^(P).width r) (cs).length i:=
  (Classical.choose_spec (IntegralMixedRoadmapRetainedAppend.parent_interpretation hn ht ha hR0 old hv hd E he)).1

theorem hom_values :∀i,hom hn ht ha hR0 old hv hd ((x).bank.numerator i)/((x).bank.denominator i:ℝ)=V i:=by
  unfold IntegralMixedRoadmapRetainedAppend.parentValues
  exact (Classical.choose_spec (IntegralMixedRoadmapRetainedAppend.parent_interpretation hn ht ha hR0 old hv hd E he)).2

theorem parent_room :(cs).length+1≤(P).cap r+1:=by
  have HR:=IntegralMixedRoadmapRetainedAppend.midpoint_room hn ht ha hR0 old hv hd E he
  have HL:=IntegralMixedRoadmapRetainedAppend.midpoint_selection_count hn ht ha hR0 old hv hd E he
  omega

noncomputable def objective :Fin ((P).ambient r+1):=
  (IntegralMixedRoadmapRetainedAppend.midpointObjective hn ht ha hR0 old hv hd E he).val

theorem objective_value :(objective hn ht ha hR0 old hv hd).val=(d).labels.length+1:=rfl

theorem objective_free :objective hn ht ha hR0 old hv hd∉
    (IntegralMixedChronologicalSweepFrame.frame d hk).frozen:=by
  apply (IntegralMixedChronologicalSweepFrame.free_iff d hk _).mpr
  exact (objective_value hn ht ha hR0 old hv hd).ge

local notation "hm"=>(Nat.le_of_succ_le (parent_room hn ht ha hR0 old hv hd))
local notation "g"=>objective hn ht ha hR0 old hv hd
local notation "hg"=>objective_free hn ht ha hR0 old hv hd
local notation "phi"=>hom hn ht ha hR0 old hv hd
local notation "rule"=>cutRule x (Descriptor.frame d) (IntegralMixedChronologicalSweepFrame.next d hk) g hg

noncomputable def choices :Choices x hm rule phi:=Classical.choice (exists_choices x hm rule phi)

theorem exists_guarded_pair (left right :Endpoint (cs).length)
    (HL :left.Allowed (jointEndpointSet x hm phi (d).frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg V (choices hn ht ha hR0 old hv hd)))
    (HR :right.Allowed (jointEndpointSet x hm phi (d).frame
      (IntegralMixedChronologicalSweepFrame.next d hk) g hg V (choices hn ht ha hR0 old hv hd))) :
    ∃R :NativePair x d z phi V left right (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) hc,
      GuardedProgram x
        (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) hc z phi V
        R.result.commands R.result.room R.result.codes R.result.tuple R.result.hom R.result.nextValues:=by
  have HDegree :(Q).degree=BoundedZeroSource.powerDegree
      (t (IntegralMixedAuxiliaryMarkedIntegerSource.original r)).toData.size:=
    IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t (radius R0) r
  exact optional_pair_guarded x hm (parent_room hn ht ha hR0 old hv hd)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha r) _ HDegree hc d hk g hg
    (objective_value hn ht ha hR0 old hv hd) z
    (IntegralMixedRoadmapRetainedAppend.parent_roots hn ht ha hR0 old hv hd E he)
    phi (hom_generators hn ht ha hR0 old hv hd) V (hom_values hn ht ha hR0 old hv hd)
    (choices hn ht ha hR0 old hv hd) left right HL HR

end LeanCanny.Encoding.IntegralMixedRoadmapProperParent

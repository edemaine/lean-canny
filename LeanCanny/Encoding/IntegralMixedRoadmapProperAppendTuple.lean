/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendObservation
/-! # The same constructed natural tuple satisfies the actual proper-append program -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius_binary)
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
attribute [local irreducible] compiledObservation canonicalObservation

theorem tuple_roots (z :ℕ→ℝ)
    (hz :(canonicalObservation hn ht ha hR0 old hv hd left right R side).Roots z):
    (compiledObservation hn ht ha hR0 old hv hd left right R side).Roots z:=
  Eq.mpr (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots z)
    (compiled_observation_eq hn ht ha hR0 old hv hd left right R side)) hz

theorem tuple_arity :(compiledObservation hn ht ha hR0 old hv hd left right R side).arity=
    (canonicalObservation hn ht ha hR0 old hv hd left right R side).arity:=
  congrArg IntegralMixedFramedRunObservation.Data.arity
    (compiled_observation_eq hn ht ha hR0 old hv hd left right R side)

theorem tuple_point (z :ℕ→ℝ) (i :ℕ):
    (compiledObservation hn ht ha hR0 old hv hd left right R side).point z i=
      (canonicalObservation hn ht ha hR0 old hv hd left right R side).point z i:=
  congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.point z i)
    (compiled_observation_eq hn ht ha hR0 old hv hd left right R side)

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

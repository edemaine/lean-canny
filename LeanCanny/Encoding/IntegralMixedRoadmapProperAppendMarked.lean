/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPastValues
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
/-! # Old raw retention preserves the original marked-input guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX" root=>IntegralMixedMarkedPrefixFieldReadback.context root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot
  IntegralMixedPhysicalFieldEquality.point

theorem marked_of_raw_retention (old :List Bool)
    (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
    (left right :List Bool) (side :Bool) (hE :EndpointsGood hn ht ha hR0 old left right) (w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid S (CTX (preparedRoot hn ht ha hR0 old left right side)) w)
    (hr :∀i<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old left right side),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0
        (preparedRoot hn ht ha hR0 old left right side) w hw i=oldNatural hn ht ha hR0 old hv i):
    pair (preparedRoot hn ht ha hR0 old left right side) w∈
      IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
  apply IntegralMixedPhysicalMarkedRetention.language_transfer_fields hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (preparedRoot hn ht ha hR0 old left right side)
    (IntegralMixedRoadmapAtomic.word old) w (old_valid_native hn ht ha hR0 old hv) hw
    (prepared_candidate hn ht ha hR0 old left right side).symm
    (fun i hi=>(past_fields hn ht ha hR0 old hv hd left right side hE w hw hr i (by
      rw [begin_eq_old_start hn ht ha hR0 old]
      omega)).symm)
  exact hv.2.2.2.2.2.2

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend

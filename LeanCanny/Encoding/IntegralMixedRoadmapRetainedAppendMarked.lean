/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPacket
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedFieldRetention
/-! # Preserved initial fields validate the appended word's marked input -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask
open IntegralMixedOriginalRegularSource (radius_binary)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot

theorem marked_of_initial_fields (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old) (e : ℕ) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (hfields : ∀i,i<number n (IntegralMixedRoadmapAtomic.root old)+8→
      IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0) (CTX old e) w hw i=
        IntegralMixedPhysicalFieldEquality.point hn ht ha (radius_binary hR0)
          (IntegralMixedRoadmapAtomic.context old) (IntegralMixedRoadmapAtomic.word old)
          (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) i) :
    pair (preparedRoot hn ht ha hR0 old e) w∈
      IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
  apply IntegralMixedPhysicalMarkedRetention.language_transfer_fields hn ht ha hR0
    (IntegralMixedRoadmapAtomic.root old) (preparedRoot hn ht ha hR0 old e)
    (IntegralMixedRoadmapAtomic.word old) w (IntegralMixedRoadmapAtomic.full_valid hn ht ha hR0 old hv) hw
    (prepared_candidate hn ht ha hR0 old e).symm
    (fun i hi=>(hfields i hi).symm)
  exact hv.2.2.2.2.2.2

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

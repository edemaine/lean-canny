/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendMarked
public import LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppendPastCritical
/-! # The old natural columns imply the appended marked-input guard -/
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
local notation "D"=>IntegralMixedRoadmapAtomic.dimension hn ht ha hR0
local notation "CTX"=>context hn ht ha hR0
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank preparedRoot
  IntegralMixedPhysicalFieldEquality.point

theorem marked_of_raw_retention (old : List Bool)
    (hv : IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (hd : IntegralMixedRoadmapAtomic.depth old<D old) (e : ℕ)
    (he : e<beginBirth hn ht ha hR0 old) (w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid S (CTX old e) w)
    (hr : ∀r<IntegralMixedFramedPhysicalIndex.arity (parentCommands hn ht ha hR0 old hv hd e he),
      IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (preparedRoot hn ht ha hR0 old e) w hw r=
        oldNatural hn ht ha hR0 old hv r) :
    pair (preparedRoot hn ht ha hR0 old e) w∈
      IntegralMixedPhysicalMarkedTest.language hn ht ha (radius_binary hR0) false:=by
  apply marked_of_initial_fields hn ht ha hR0 old hv e w hw
  intro i hi
  have HF:=past_fields hn ht ha hR0 old hv hd e he w hw hr i (by omega)
  exact HF

end LeanCanny.Encoding.IntegralMixedRoadmapRetainedAppend

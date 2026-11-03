/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperNearNative
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareComposition
/-! # Proper row words and field-scan words use the same full ordinal sample

Only the query indexing changes. The prepared ROOT is unchanged here;
ordinary and mean ROOTS continue to use independent full words.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem sampler_comp (mean : Bool) :
    IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)=
      SquareSampleInput.comp S (context hn ht ha hR0 mean) :=
  IntegralFramedPhysicalSquare.input_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context hn ht ha hR0 mean)

theorem valid_at_context (mean : Bool) (z w : List Bool) :SquareSampleCompleteVertices.Valid
    (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)) z w↔
      SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w :=by
  rw [sampler_comp]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem natural_at_context (mean : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)) z w)
    (hc : SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w) :
    IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) z w hv=
      IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (context hn ht ha hR0 mean z) w hc :=
  IntegralFramedPhysicalSquare.naturalPoint_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context hn ht ha hR0 mean) z w hv hc


theorem point_at_context (mean : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean)) z w)
    (hc : SquareSampleCompleteVertices.Valid S (context hn ht ha hR0 mean z) w) :
    IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal hn ht ha hR0 mean) (positive hn ht ha hR0 mean) z w hv=
      IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (context hn ht ha hR0 mean z) w hc :=
  IntegralFramedPhysicalSquare.point_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context hn ht ha hR0 mean) z w hv hc

end LeanCanny.Encoding.IntegralMixedRoadmapProperRow

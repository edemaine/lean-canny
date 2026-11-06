/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperNearNative
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareComposition
/-! # Proper row words and field-scan words use the same full ordinal sample

Only the query indexing changes. The prepared ROOT is unchanged here;
ordinary and mean ROOTS continue to use independent full words.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B"=>FormulaSignSlotRadialProviderRecordPlan.bank
local notation "S"=>FormulaSignSlotRadialProviderAtomic.input
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family

theorem sampler_comp (mean : Bool) :
    IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal mean) (positive mean)=
      SquareSampleInput.comp S (context mean) :=
  IntegralFramedPhysicalSquare.input_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context mean)

theorem valid_at_context (mean : Bool) (z w : List Bool) :SquareSampleCompleteVertices.Valid
    (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal mean) (positive mean)) z w↔
      SquareSampleCompleteVertices.Valid S (context mean z) w :=by
  rw [sampler_comp]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem natural_at_context (mean : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal mean) (positive mean)) z w)
    (hc : SquareSampleCompleteVertices.Valid S (context mean z) w) :
    IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal mean) (positive mean) z w hv=
      IntegralFramedPhysicalSquare.naturalPoint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (context mean z) w hc :=
  IntegralFramedPhysicalSquare.naturalPoint_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context mean) z w hv hc


theorem point_at_context (mean : Bool) (z w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid
      (IntegralFramedPhysicalSquare.input (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (terminal mean) (positive mean)) z w)
    (hc : SquareSampleCompleteVertices.Valid S (context mean z) w) :
    IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
      (terminal mean) (positive mean) z w hv=
      IntegralFramedPhysicalSquare.point (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (context mean z) w hc :=
  IntegralFramedPhysicalSquare.point_comp (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive (context mean) z w hv hc

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperRow

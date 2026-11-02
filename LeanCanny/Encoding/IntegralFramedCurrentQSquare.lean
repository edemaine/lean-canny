/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCompleteSquareSpace
public import LeanCanny.Encoding.SquareSampleCompleteVertices
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace

/-! # Joint scalar-prefix vertices from the actual current-Q native backend

Critical instructions are allowed. The row reader comes from their literal
creating companion and the charged current-bank product. No matrix reader,
root regularity or all-noncritical hypothesis is supplied.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCurrentQSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedStepHeight
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)

 theorem access (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<(family P D H).birth (key u))
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c) :
    (IntegralFramedCompleteSquare.input P D H L F C h key hpos).Access :=
  IntegralFramedCompleteSquare.access P a D H L F C h hL hF hC key hk hpos
    (IntegralFramedCompleteSquare.row_evaluator P a D H L F C h key hk hpos
      (IntegralMixedFramedCurrentQCompanionBits.evaluator P a D H Hnew c hb))

theorem valid_decider (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (h : FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ u,0<(family P D H).birth (key u))
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c) :
    SpaceDecider (SquareSampleCompleteVertices.language (IntegralFramedCompleteSquare.input P D H L F C h key hpos)) :=
  SquareSampleCompleteVertices.decider (access P a D H L F C h hL hF hC key hk hpos Hnew c hb)

end LeanCanny.Encoding.IntegralFramedCurrentQSquare

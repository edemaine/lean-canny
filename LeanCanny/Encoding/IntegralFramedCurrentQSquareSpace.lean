/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQCompanionSpace
public import LeanCanny.Encoding.IntegralFramedCompleteSquareSpace
/-! # Native complete-square access from actual current-Q original controls

The caller-modulus root pullback supplies the actual creating companion
source. Every literal prefix row is then derived through its own creator;
no row, annihilator, coefficient or current-matrix evaluator is input.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCurrentQSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)

theorem access_native (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted P) (liftedPlan P D))
    (c : IntegralMixedFramedCurrentQNativeBits.Controls (lifted P) (liftedPlan P D) Hnew)
    (hb : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted P) (liftedPlan P D) Hnew c)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (key : List Bool→List Bool) (hk : key∈FP)
    (hpos : ∀ q,0<(IntegralMixedFramedHistoryFamilyBits.family P D H).birth (key q)) :
    (IntegralFramedCompleteSquare.input P D H L F C hs key hpos).Access :=
  IntegralFramedCompleteSquare.access P a D H L F C hs hL hF hC key hk hpos
    (IntegralFramedCompleteSquare.row_evaluator P a D H L F C hs key hk hpos
      (IntegralMixedFramedCurrentQCompanionBits.evaluator P a D H Hnew c hb))

end LeanCanny.Encoding.IntegralFramedCurrentQSquare

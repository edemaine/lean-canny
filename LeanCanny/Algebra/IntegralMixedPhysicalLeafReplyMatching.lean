/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDerivative
/-! # One actual original-leaf match closes current physical derivatives

The child is the guarded fixed-width bumped original coefficient. Its
fresh writer preserves the actual saved prefix and routine, sets phase
zero, and decreases the mixed rank. No derivative evaluator is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev OriginalMatches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ q, selected P .originalCoefficient q = true → reply q = original P F q

theorem derivative_original_selected (P : Parameters) (F : Family) (q : List Bool)
    (hq : selected P .derivativeCoefficient q = true) :
    selected P .originalCoefficient (IntegralCriticalFlatDerivativeQuery.writer P
      (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q))) = true := by
  let z := IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)
  have HO : IntegralDerivativeBits.original z = q :=
    (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans
      (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
  apply (selected_iff P .originalCoefficient _).mpr
  constructor
  · have HR : IntegralMixedRoutineTaskBits.routine P (IntegralCriticalFlatDerivativeQuery.writer P z) =
        IntegralMixedRoutineTaskBits.routine P (IntegralDerivativeBits.original z) := by
      unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatDerivativeQuery.writer_other P z .slot14 (by decide) (by decide) (by decide)]
    rw [HR, HO]
    exact ((selected_iff P .derivativeCoefficient q).mp hq).1
  · exact IntegralCriticalFlatDerivativeQuery.writer_phase P z

theorem derivative_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (he : OriginalMatches P F reply) (q : List Bool) (hq : selected P .derivativeCoefficient q = true) :
    DerivativeRepliesAt P F reply q := by
  intro _
  exact he _ (derivative_original_selected P F q hq)

theorem derivative_correct_of_original (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : OriginalMatches P F reply) :
    Correct (derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  derivative_correct P a F h g reply (derivative_replies P F reply he)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits

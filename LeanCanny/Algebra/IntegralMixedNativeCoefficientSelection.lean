/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNativeCoefficient
/-! # Actual critical coefficients use relative powers and charged scalar leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev RelativePowerMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → isPhase .relativePower q →
    answer q = (characteristic P F).value q

theorem coefficient_replies (P : Parameters) (F : Family) (answer : List Bool → List Bool)
    (hx : RelativePowerMatches P F answer) (hl : LeadingMatches P F answer) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) :
    CoefficientRepliesAt P F answer q := by
  constructor
  · have HV : IntegralMixedVirtualCaps.valid P (IntegralCriticalFlatEulerBits.next P .relativePower q) := by
      unfold IntegralMixedVirtualCaps.valid
      rw [IntegralCriticalFlatEulerBits.next_birth, IntegralCriticalFlatEulerBits.next_root]
      exact hv
    have HR : IntegralMixedRoutineTaskBits.routine P (IntegralCriticalFlatEulerBits.next P .relativePower q) = 1 := by
      unfold IntegralMixedRoutineTaskBits.routine
      rw [IntegralCriticalFlatEulerBits.next_get]
      simpa only [IntegralMixedRoutineTaskBits.routine] using hr
    exact (hx _ HV HR (IntegralCriticalFlatEulerBits.next_phase P .relativePower q)).trans (characteristic_next P F .relativePower q)
  · have HV : IntegralMixedVirtualCaps.valid P (IntegralMixedScalarQueryBits.commonLeading P q) := by
      unfold IntegralMixedVirtualCaps.valid IntegralMixedScalarQueryBits.commonLeading
      rw [IntegralMixedRoutineTaskBits.query_birth P (birth P) .scalar .monomialFactor q (min_le_right _ _),
        IntegralMixedRoutineTaskBits.query_root]
      exact hv
    exact (hl _ HV (IntegralMixedRoutineTaskBits.query_routine P (birth P) .scalar .monomialFactor q)
      (IntegralMixedRoutineTaskBits.query_phase P (birth P) .scalar .monomialFactor q)).trans (commonLeading_child P F q)

theorem correct25_of_matches (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool)
    (hx : RelativePowerMatches P F answer) (hl : LeadingMatches P F answer) :
    Correct (stage25 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply correct25 P a F h answer
  intro q hq
  have H := (selected_iff P .criticalCoefficient q).mp hq
  exact coefficient_replies P F answer hx hl q H.1 H.2.1

end LeanCanny.Algebra.IntegralMixedVirtualUpperBits

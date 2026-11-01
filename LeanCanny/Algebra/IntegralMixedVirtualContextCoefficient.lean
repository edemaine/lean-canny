/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralScaledCharacteristicChargedController
public import LeanCanny.Algebra.IntegralMixedVirtualContextAction
public import LeanCanny.Algebra.IntegralMixedVirtualContextRelativePower
/-! # Actual virtual critical coefficients with a charged leading child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
open IntegralMixedVirtualUpperBits
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientExponent (P : Parameters) (F : Family) (q : List Bool) : ℕ := (relative P F).layout.bound q + 1

theorem coefficientExponent_binary (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : BinaryFn (coefficientExponent P F) :=
  (relativeAccess P a F h).bound.add (BinaryFn.const 1)

theorem critical_scaled (P : Parameters) (F : Family) (q : List Bool) :
    IntegralScaledCharacteristicBits.value (characteristic P F) (relative P F).leading (coefficientExponent P F) q =
      (critical P F).value q := congrFun (IntegralPurePowerActionBits.polynomial_value (relative P F)) q

theorem leading_residue (P : Parameters) (F : Family) (q : List Bool) :
    commonLeading P F q = residueBits ((relative P F).leading q : ZMod ((characteristic P F).modulus q)) := rfl

noncomputable def coefficientProgram (P : Parameters) (F : Family) :=
  IntegralScaledCharacteristicBits.Charged.program (characteristic P F) (coefficientExponent P F)
    (IntegralCriticalFlatEulerBits.next P .relativePower) (IntegralMixedScalarQueryBits.commonLeading P)

theorem coefficient_certificates (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) :
    (coefficientProgram P F).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  IntegralScaledCharacteristicBits.Charged.certificates (characteristic P F) (characteristicAccess P a F h)
    (coefficientExponent P F) (coefficientExponent_binary P a F h) _ _
    (IntegralCriticalFlatEulerBits.next_FP P a .relativePower) (IntegralMixedScalarQueryBits.scalarQuery_FP P a .monomialFactor)

structure CoefficientRepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop where
  coefficient : answer (IntegralCriticalFlatEulerBits.next P .relativePower q) = (characteristic P F).value q
  leading : answer (IntegralMixedScalarQueryBits.commonLeading P q) = commonLeading P F q

theorem value25 (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (he : CoefficientRepliesAt P F answer q) :
    (coefficientProgram P F).value answer q = (critical P F).value q :=
  (IntegralScaledCharacteristicBits.Charged.value_at (characteristic P F) (relative P F).leading
    (coefficientExponent P F) _ _ answer q he.coefficient (he.leading.trans (leading_residue P F q))).trans (critical_scaled P F q)

noncomputable def stage25 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (coefficientProgram P F).controller
  certificates := coefficient_certificates P a F h
  selected := selected P .criticalCoefficient
  selected_FP := selected_FP P a .criticalCoefficient
  model := (critical P F).value
  clock _ := 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralScaledCharacteristicBits.Charged.stateBound (characteristic P F)
  stateBound_unary := IntegralScaledCharacteristicBits.Charged.stateBound_unary (characteristic P F) (characteristicAccess P a F h)

theorem correct25 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (answer : List Bool → List Bool) (he : ∀ q, selected P .criticalCoefficient q = true → CoefficientRepliesAt P F answer q) :
    Correct (stage25 P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (coefficientProgram P F).halted_after answer q
  · intro q t hq hh
    exact ((coefficientProgram P F).output_when_halted answer q t hh).trans (value25 P F answer q (he q hq))
  · intro q t hq
    have H := he q hq
    exact IntegralScaledCharacteristicBits.Charged.state_length_at (characteristic P F) (relative P F).leading
      (coefficientExponent P F) _ _ answer q H.coefficient (H.leading.trans (leading_residue P F q)) t
  · intro q c budget hq hc
    have H := selected_base P .criticalCoefficient q hq
    rcases IntegralScaledCharacteristicBits.Charged.requests_cases (characteristic P F) (coefficientExponent P F)
      _ _ answer budget q c hc with rfl | rfl
    · apply frame_of_tasks_same_routine P q _
      · unfold IntegralMixedRoutineTaskBits.routine
        rw [IntegralCriticalFlatEulerBits.next_get]
      · exact IntegralCriticalFlatEulerBits.next_tasks P .relativePower q q (tasks_self P q)
      · apply IntegralCriticalFlatEulerBits.next_lower_rank
        have HP := H.2.2
        change phase q = 25 at HP
        change 24 < phase q
        omega
    · exact IntegralMixedScalarQueryBits.scalar_frame P .monomialFactor q (by rw [H.2.1]; decide)

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueHomogeneousActual

/-! # Actual homogeneous value-row native branch at routine two, phase 22

The model is the literal homogeneous multiplication-matrix entry, with
zero at invalid labels. Current smaller-task replies name only the
constructed restored-row or virtual critical-coefficient source.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousBranch
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps
open IntegralMixedValueHomogeneousPoint
open scoped Classical

def Selected (P : Parameters) (q : List Bool) : Prop :=
  valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ isPhase .momentPower q
noncomputable instance (P : Parameters) (q : List Bool) : Decidable (Selected P q) := inferInstanceAs (Decidable (_ ∧ _))

theorem selected_FP (P : Parameters) (a : Access P) : FPPred (Selected P) :=
  (valid_FP P a).and ((((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2))).and
    (isPhase_FP .momentPower))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := SingleCall.State
  defaultValue := default
  encoding := SingleCall.encState
  controller := (IntegralMixedValueHomogeneousRequest.program P F).controller
  certificates := IntegralMixedValueHomogeneousRequest.certificates P a F h
  selected q := decide (Selected P q)
  selected_FP := (selected_FP P a).flag_mem_FP
  model := IntegralMixedValueHomogeneousMatrix.value P F
  clock _ := 1
  clock_binary := BinaryFn.const 1
  stateBound := IntegralMixedValueHomogeneousRequest.stateBound P
  stateBound_unary := IntegralMixedValueHomogeneousRequest.stateBound_unary P a

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (hr : ∀ q, Selected P q → RepliesAt P F reply q) :
    Correct (machine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (IntegralMixedValueHomogeneousRequest.program P F).halted_after reply q
  · intro q t hq hh
    have HS : Selected P q := of_decide_eq_true hq
    exact ((IntegralMixedValueHomogeneousRequest.program P F).output_when_halted reply q t hh).trans
      (IntegralMixedValueHomogeneousActual.value_at P F g reply q (hr q HS))
  · intro q t hq
    have HS : Selected P q := of_decide_eq_true hq
    exact IntegralMixedValueHomogeneousActual.state_length P F reply q t (hr q HS)
  · intro q c budget hq hc
    have HS : Selected P q := of_decide_eq_true hq
    exact IntegralMixedValueHomogeneousRequest.requests_frame P F reply budget q c HS.2.1 HS.2.2 hc

end LeanCanny.Algebra.IntegralMixedValueHomogeneousBranch

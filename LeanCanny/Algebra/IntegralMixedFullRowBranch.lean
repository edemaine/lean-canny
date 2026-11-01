/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedFullRowLowerChild
public import LeanCanny.Algebra.IntegralMixedFullRowScalarChild

/-! # Actual full-row branch with native lower and scalar child models

Routine two, phase 21, restores the original source row. Its concrete child
models are the existing frozen-low or cleared-gradient stage and the
existing original-scale or common-leading scalar stage. Correctness uses
only current replies to those smaller tasks, with no computation premise
for a full row or a matrix entry.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullRowBranch
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedFullRowTasks
open scoped Classical

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  reply (lowTask P F q) = IntegralMixedFullRowLowerChild.model P F q ∧
  reply (scalarTask P F q) = IntegralMixedFullRowScalarChild.model P F q

theorem replies (P : Parameters) (F : Family) (h : RootGeometry P F) (reply : List Bool → List Bool) (q : List Bool)
    (hr : RepliesAt P F reply q) : IntegralMixedFullRowNative.RepliesAt P F reply q :=
  ⟨hr.1.trans (IntegralMixedFullRowLowerChild.model_eq P F h q), hr.2.trans (IntegralMixedFullRowScalarChild.model_eq P F q)⟩

def Selected (P : Parameters) (q : List Bool) : Prop :=
  valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ isPhase .momentEntry q
noncomputable instance (P : Parameters) (q : List Bool) : Decidable (Selected P q) := inferInstanceAs (Decidable (_ ∧ _))

theorem selected_FP (P : Parameters) (a : Access P) : FPPred (Selected P) :=
  (valid_FP P a).and ((((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2))).and
    (isPhase_FP .momentEntry))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralMixedFullRowNative.program P F).controller
  certificates := IntegralMixedFullRowNative.certificates P a F h
  selected q := decide (Selected P q)
  selected_FP := (selected_FP P a).flag_mem_FP
  model := IntegralMixedValueRestoredSource.value P F
  clock _ := 2
  clock_binary := BinaryFn.const 2
  stateBound := IntegralMixedFullRowRequest.stateBound (family P F) (indices P F)
  stateBound_unary := IntegralMixedFullRowNative.stateBound_unary P a F h

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (hr : ∀ q, Selected P q → RepliesAt P F reply q) :
    Correct (machine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact (IntegralMixedFullRowNative.program P F).halted_after reply q
  · intro q t hq hh
    have HS : Selected P q := of_decide_eq_true hq
    exact ((IntegralMixedFullRowNative.program P F).output_when_halted reply q t hh).trans
      (IntegralMixedFullRowNative.value_at P F reply q (replies P F g reply q (hr q HS)))
  · intro q t hq
    have HS : Selected P q := of_decide_eq_true hq
    exact IntegralMixedFullRowNative.state_length P F reply q (replies P F g reply q (hr q HS)) t
  · intro q c budget hq hc
    have HS : Selected P q := of_decide_eq_true hq
    have HC := IntegralMixedVirtualNativeLowerBits.fold_requests_bound (IntegralMixedFullRowNative.program P F) reply budget q c hc
    exact IntegralMixedFullRowNative.requests_frame P F reply q c HS.2.1 HC

end LeanCanny.Algebra.IntegralMixedFullRowBranch

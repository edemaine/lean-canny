/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineTask
public import LeanCanny.Algebra.IntegralMixedVirtualOriginalLeaf
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # A concrete charged integer leaf for virtual critical arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev source (P : Parameters) (F : Family) := IntegralMixedVirtualTaskBits.arithmetic P F
noncomputable abbrev sourceAccess (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :=
  (IntegralMixedVirtualTaskBits.access P a F h).toEuler

def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedRoutineTaskBits.routine P q = IntegralMixedRoutineTaskBits.Routine.critical.code ∧ isPhase p q)

theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 1)).and (isPhase_FP p)).flag_mem_FP

theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedRoutineTaskBits.routine P q = 1 ∧ isPhase p q := by
  simp only [selected, decide_eq_true_eq, IntegralMixedRoutineTaskBits.Routine.code]

noncomputable def answer (P : Parameters) (x : (q : List Bool) → ZMod (modulus P q)) (q : List Bool) := residueBits (x q)

noncomputable abbrev originalScalar (P : Parameters) (F : Family) :=
  IntegralMixedVirtualOriginalBits.scalar (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)
noncomputable abbrev original (P : Parameters) (F : Family) :=
  IntegralMixedVirtualOriginalBits.value P (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)

noncomputable def originalProgram (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := false
  query := id
  immediate := original P F
  finish := id

theorem original_certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) :
    (originalProgram P F).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (originalProgram P F).certificates_of_space (constFn_mem_FP [false]) id_mem_FP
    (IntegralMixedVirtualOriginalBits.value_space P a _ _ (IntegralMixedVirtualTaskBits.metadata P a F h) ha).computable
    (SpaceFunction.ofFP _ id_mem_FP).computable

noncomputable def originalMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine :=
  ofSingleCall (originalProgram P F) (original_certificates P a F h ha)
    (selected P .originalCoefficient) (selected_FP P a .originalCoefficient) (original P F) (fun _ => 0) (UnaryFn.const 0)

theorem original_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (reply : List Bool → List Bool) :
    Correct (originalMachine P a F h ha) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _
    rfl
  · intro q _ hr
    cases hr
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((originalProgram P F).requests_iff reply budget q c).mp hc
    cases hr
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits

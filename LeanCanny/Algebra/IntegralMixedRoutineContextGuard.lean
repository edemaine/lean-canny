/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualCaps
public import LeanCanny.Algebra.IntegralMixedRoutineTask
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # Native guards for a fixed mixed routine and producer-context interval -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRoutineContextGuard
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Selected (P : Parameters) (code lo hi : ℕ) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = code ∧
    lo ≤ get P .slot15 q ∧ get P .slot15 q ≤ hi

theorem selected_FP (P : Parameters) (a : Access P) (code lo hi : ℕ) : FPPred (Selected P code lo hi) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const code)).and
      (((BinaryFn.const lo).le (get_binary P a .slot15)).and ((get_binary P a .slot15).le (BinaryFn.const hi))))

noncomputable def machine (P : Parameters) (a : Access P) (code lo hi : ℕ) (M : Machine) : Machine :=
  M.withGuard (fun q => decide (Selected P code lo hi q)) (selected_FP P a code lo hi).flag_mem_FP

theorem correct (P : Parameters) (a : Access P) (code lo hi : ℕ) (M : Machine)
    (answer : List Bool → List Bool) (frame : List Bool → List Bool → Prop)
    (hm : Correct M answer frame) (hs : ∀ q, M.selected q = true) :
    Correct (machine P a code lo hi M) answer frame :=
  withGuard_correct M _ _ answer frame hm (fun q _ => hs q)

end LeanCanny.Algebra.IntegralMixedRoutineContextGuard

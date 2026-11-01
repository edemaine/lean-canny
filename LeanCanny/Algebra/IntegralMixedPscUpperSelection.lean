/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicBounds
/-! # Native PSC determinant headers and disjoint arithmetic phases -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

def Domain (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 3 ∧
    get P .slot15 q = 3 ∧ get P .slot8 q < IntegralMixedPscEntryBits.degree P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Domain P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem domain_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Domain P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 3)).and
      (((get_binary P a .slot15).eq (BinaryFn.const 3)).and
        ((get_binary P a .slot8).lt (IntegralMixedPscEntryBits.degree_binary P a F h))))
noncomputable def selected (P : Parameters) (F : Family) (p : Phase) (q : List Bool) : Bool :=
  decide (Domain P F q ∧ isPhase p q)
theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (p : Phase) :
    (fun q => [selected P F p q]) ∈ FP := ((domain_FP P a F h).and (isPhase_FP p)).flag_mem_FP

theorem selected_iff (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    selected P F p q = true ↔ Domain P F q ∧ isPhase p q := by
  simp only [selected, decide_eq_true_eq]

end LeanCanny.Algebra.IntegralMixedPscUpperBits

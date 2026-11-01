/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryActual
/-! # Native routine-two PSC entries have actual local semantics -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] value coefficientValue

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧
    isPhase .originalCoefficient q ∧ get P .slot15 q = 3 ∧ get P .slot8 q < degree P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Selected P F q) := inferInstanceAs (Decidable (_ ∧ _))
theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2)).and
      ((isPhase_FP .originalCoefficient).and (((get_binary P a .slot15).eq (BinaryFn.const 3)).and
        ((get_binary P a .slot8).lt (degree_binary P a F h)))))

theorem replyBound_unary (P : Parameters) (a : Access P) : UnaryFn (fun q => (modulus P q).size) :=
  (UnaryFn.length (modulus_binary P a).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofSingleCall (program P F) ((program P F).certificates (program_controls P a F h))
    (fun q => decide (Selected P F q)) (selected_FP P a F h).flag_mem_FP (value P F)
    (fun q => (modulus P q).size) (replyBound_unary P a)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (answer : List Bool → List Bool)
    (he : ∀ q, Selected P F q → RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold machine
  apply ofSingleCall_correct
  · intro q hs
    exact actual_value_at P F g answer q (he q (of_decide_eq_true hs))
  · intro q hs hr
    have HQ : Request P F q := of_decide_eq_true hr
    have HH := he q (of_decide_eq_true hs) HQ
    change (answer (query P F q)).length ≤ _
    rw [HH, child_value P F g q HQ]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hs hc
    have HS : Selected P F q := of_decide_eq_true hs
    obtain ⟨_, HE⟩ := ((program P F).requests_iff answer budget q c).mp hc
    rw [HE]
    exact query_frame P F q HS.2.1

end LeanCanny.Algebra.IntegralMixedPscEntryBits

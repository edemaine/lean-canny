/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscEntryClosure
/-! # The actual PSC entry is available in every virtual creating context -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscEntryScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedPscEntryBits.value

def Selected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧ isPhase .originalCoefficient q ∧
    IntegralMixedVirtualContextBits.context P q ∧ get P .slot8 q < IntegralMixedPscEntryBits.degree P F q

theorem selected_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Selected P F) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 2)).and
      ((isPhase_FP .originalCoefficient).and ((IntegralMixedVirtualContextBits.context_FP P a).and
        ((get_binary P a .slot8).lt (IntegralMixedPscEntryBits.degree_binary P a F h)))))

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofSingleCall (IntegralMixedPscEntryBits.program P F)
    ((IntegralMixedPscEntryBits.program P F).certificates (IntegralMixedPscEntryBits.program_controls P a F h))
    (fun q => decide (Selected P F q)) (selected_FP P a F h).flag_mem_FP (IntegralMixedPscEntryBits.value P F)
    (fun q => (modulus P q).size) (IntegralMixedPscEntryBits.replyBound_unary P a)

theorem selected_iff (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).selected q = true ↔ Selected P F q := by
  change decide (Selected P F q) = true ↔ Selected P F q
  simp only [decide_eq_true_eq]

theorem model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    (machine P a F h).model q = IntegralMixedPscEntryBits.value P F q := rfl

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (he : ∀ q, Selected P F q → IntegralMixedPscEntryBits.RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q hs
    exact IntegralMixedPscEntryBits.actual_value_at P F g answer q (he q (of_decide_eq_true hs))
  · intro q hs hr
    have HQ : IntegralMixedPscEntryBits.Request P F q := of_decide_eq_true hr
    have HH := he q (of_decide_eq_true hs) HQ
    change (answer (IntegralMixedPscEntryBits.query P F q)).length ≤ _
    rw [HH, IntegralMixedPscEntryBits.child_value P F g q HQ]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hs hc
    have HS : Selected P F q := of_decide_eq_true hs
    obtain ⟨_, HE⟩ := ((IntegralMixedPscEntryBits.program P F).requests_iff answer budget q c).mp hc
    rw [HE]
    exact IntegralMixedPscEntryBits.query_frame P F q HS.2.1

theorem child_context (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hr : IntegralMixedPscEntryBits.Request P F q) :
    get P .slot15 (IntegralMixedPscEntryBits.query P F q) = get P .slot15 q := by
  simp only [IntegralMixedPscEntryBits.query_get P F g q hr, reduceCtorEq, ite_false]

theorem child_selected (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hs : Selected P F q) (hr : IntegralMixedPscEntryBits.Request P F q) :
    IntegralMixedVirtualContextBits.selected P .criticalCoefficient (IntegralMixedPscEntryBits.query P F q) = true := by
  apply decide_eq_true
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P id .critical .criticalCoefficient .coefficient _ q,
    IntegralMixedValueFieldQuery.query_phase P id .critical .criticalCoefficient .coefficient _ q, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [IntegralMixedPscEntryBits.query_root, IntegralMixedPscEntryBits.query_birth]
    exact hs.1
  · unfold IntegralMixedVirtualContextBits.context
    rw [child_context P F g q hr]
    exact hs.2.2.2.1

theorem replies_of_matches (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer)
    (q : List Bool) (hs : Selected P F q) : IntegralMixedPscEntryBits.RepliesAt P F answer q := by
  intro hr
  have H := own .criticalCoefficient (IntegralMixedPscEntryBits.query P F q) (by decide) (child_selected P F g q hs hr)
  change answer (IntegralMixedPscEntryBits.query P F q) = (IntegralMixedVirtualTaskBits.source P F).value (IntegralMixedPscEntryBits.query P F q) at H
  exact H

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedVirtualContextComponentBits.Matches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h g answer (fun q hs => replies_of_matches P F g answer own q hs)

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h).model q := by
  rw [model]
  unfold IntegralMixedPscEntryBits.value
  exact ⟨_, rfl⟩
end LeanCanny.Algebra.IntegralMixedPscEntryScopedBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscActionNative
public import LeanCanny.Algebra.IntegralMixedPscContextSelection
/-! # Native determinant phase zero uses only current actual PSC entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscContextActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedPscActionTasks
open IntegralMixedPscActionBits
open scoped Classical
attribute [local irreducible] IntegralMixedPscActionBits.value

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofSingleCall (program P F) ((program P F).certificates (controls P a F h))
    (IntegralMixedPscContextUpperBits.selected P F .originalCoefficient)
    (IntegralMixedPscContextUpperBits.selected_FP P a F h .originalCoefficient) (value P F)
    (fun q => (modulus P q).size) (IntegralMixedPscEntryBits.replyBound_unary P a)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool)
    (he : ∀ q, IntegralMixedPscContextUpperBits.selected P F .originalCoefficient q = true → RepliesAt P F answer q) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold machine
  apply ofSingleCall_correct
  · intro q hs
    exact value_at P F answer q (he q hs)
  · intro q hs _
    change (answer (query P F q)).length ≤ _
    rw [he q hs, positive_child]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hs hc
    obtain ⟨_, HE⟩ := ((program P F).requests_iff answer budget q c).mp hc
    rw [HE]
    exact query_frame P F q ((IntegralMixedPscContextUpperBits.selected_iff P F .originalCoefficient q).mp hs).1.2.1

def EntrySelected (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 2 ∧
    isPhase .originalCoefficient q ∧ IntegralMixedVirtualContextBits.context P q ∧
      get P .slot8 q < IntegralMixedPscEntryBits.degree P F q
abbrev EntryMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, EntrySelected P F q → answer q = IntegralMixedPscEntryBits.value P F q

theorem child_selected (P : Parameters) (F : Family) (q : List Bool)
    (hs : IntegralMixedPscContextUpperBits.selected P F .originalCoefficient q = true) :
    EntrySelected P F (query P F q) := by
  have HH := (IntegralMixedPscContextUpperBits.selected_iff P F .originalCoefficient q).mp hs
  refine ⟨?_, IntegralMixedValueFieldQuery.query_routine P (third P F) .pscEntry .originalCoefficient .col _ q,
    IntegralMixedValueFieldQuery.query_phase P (third P F) .pscEntry .originalCoefficient .col _ q, ?_, ?_⟩
  · unfold IntegralMixedVirtualCaps.valid
    rw [query_root, query_birth]
    exact HH.1.1
  · simpa only [IntegralMixedVirtualContextBits.context, query_get, reduceCtorEq, ite_false] using HH.1.2.2.1
  · have HD : IntegralMixedPscEntryBits.degree P F (query P F q) = IntegralMixedPscEntryBits.degree P F q := by
      change IntegralMixedCoordinateSquarefree.coordinateDegree
        (F.spatial (IntegralMixedVirtualTaskBits.saved P (query P F q)))
        (F.rule (IntegralMixedVirtualTaskBits.saved P (query P F q))) = _
      rw [query_saved]
      rfl
    rw [HD]
    simpa only [query_get, reduceCtorEq, ite_false] using HH.1.2.2.2

theorem correct_of_matches (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool) (entries : EntryMatches P F answer) :
    Correct (machine P a F h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h answer (fun q hs => entries _ (child_selected P F q hs))

end LeanCanny.Algebra.IntegralMixedPscContextActionBits

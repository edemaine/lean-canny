/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscActionNative
public import LeanCanny.Algebra.IntegralMixedPscUpperSelection
/-! # Native determinant phase zero uses only current actual PSC entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedPscActionTasks
open scoped Classical
attribute [local irreducible] value

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofSingleCall (program P F) ((program P F).certificates (controls P a F h))
    (IntegralMixedPscUpperBits.selected P F .originalCoefficient)
    (IntegralMixedPscUpperBits.selected_FP P a F h .originalCoefficient) (value P F)
    (fun q => (modulus P q).size) (IntegralMixedPscEntryBits.replyBound_unary P a)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (answer : List Bool → List Bool)
    (he : ∀ q, IntegralMixedPscUpperBits.selected P F .originalCoefficient q = true → RepliesAt P F answer q) :
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
    exact query_frame P F q ((IntegralMixedPscUpperBits.selected_iff P F .originalCoefficient q).mp hs).1.2.1

end LeanCanny.Algebra.IntegralMixedPscActionBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPreparedSquarefreeNative
/-! # The prepared squarefree branch returns the literal truncated raw source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPreparedSquarefreeNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch RecursiveController
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedRawKindBits.prepare IntegralMixedSquarefreeCoefficientTasks.query

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : IntegralMixedSquarefreeCoefficientNative.FactorMatches P F answer) :
    Correct (machine P a F h k hd) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    have hs : Selected P F q := of_decide_eq_true hq
    have hk := kernel_selected P F g q hs
    have he := IntegralMixedSquarefreeCoefficientNative.replies_of_matches P F g answer own _ hk
    exact (IntegralMixedSquarefreeCoefficientNative.value_at P F g answer _ hk.1 he).trans
      (raw_value P F g q hs)
  · intro q hq hp
    have hs : Selected P F q := of_decide_eq_true hq
    have hk := kernel_selected P F g q hs
    have hl : IntegralMixedSquarefreeCoefficientTasks.Labels P F (IntegralMixedRawKindBits.prepare P F q) := of_decide_eq_true hp
    have he := IntegralMixedSquarefreeCoefficientNative.replies_of_matches P F g answer own _ hk hl
    change (answer (IntegralMixedSquarefreeCoefficientTasks.query P F (IntegralMixedRawKindBits.prepare P F q))).length ≤ replyWidth P q
    rw [he, IntegralMixedSquarefreeCoefficientValue.child_value P F g _ hk.1 hl]
    let : NeZero (modulus P (IntegralMixedRawKindBits.prepare P F q)) := ⟨modulus_ne_zero P _⟩
    exact (IntegralMixedSquarefreeCoefficientValue.value_length P F _).trans_eq
      (congrArg Nat.size (IntegralMixedRawKindBits.prepare_modulus P F q))
  · intro q c budget hq hc
    have hs : Selected P F q := of_decide_eq_true hq
    have he := (Controller.prepare_requests_iff (IntegralMixedSquarefreeCoefficientNative.program P F).controller
      (IntegralMixedRawKindBits.prepare P F) answer budget q c).mp hc
    have hchild := ((SingleCall.Program.requests_iff (IntegralMixedSquarefreeCoefficientNative.program P F)
      answer (fun _ => budget q) (IntegralMixedRawKindBits.prepare P F q) c).mp he).2
    change c = IntegralMixedSquarefreeCoefficientTasks.query P F (IntegralMixedRawKindBits.prepare P F q) at hchild
    rw [hchild]
    exact IntegralMixedRawKindBits.prepare_frame P F q _ hs.2.1 hs.2.2.1
      (IntegralMixedSquarefreeCoefficientTasks.query_frame P F _ (IntegralMixedRawKindBits.prepare_routine P F q)
        (IntegralMixedRawKindBits.prepare_phase P F q))

end LeanCanny.Algebra.IntegralMixedPreparedSquarefreeNative

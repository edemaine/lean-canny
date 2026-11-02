/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPreparedValueNative
public import LeanCanny.Algebra.IntegralMixedValueFactorScoped
/-! # The prepared value branch returns the literal truncated raw source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPreparedValueNative
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch RecursiveController
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedRawKindBits.prepare IntegralMixedValueCoefficientTasks.query

theorem replies_prepared_scoped (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool)
    (own : ∀ q, IntegralMixedValueFactorScopedBits.Selected P F q → answer q = IntegralMixedValueFactorValue.value P F q)
    (q : List Bool) (hs : Selected P F q) :
    IntegralMixedValueCoefficientNative.RepliesAt P F answer (IntegralMixedRawKindBits.prepare P F q) := by
  intro hl
  have hk := kernel_selected P F g q hs
  apply own
  refine ⟨IntegralMixedValueCoefficientNative.child_selected P F g _ hk hl, ?_⟩
  have hx := (IntegralMixedRawKindBits.prepare_context P F g q).mpr hs.2.2.2.1
  unfold IntegralMixedVirtualContextBits.context
  simpa only [IntegralMixedVirtualContextBits.context, IntegralMixedValueCoefficientTasks.query_get P F g _ hk.1 hl, reduceCtorEq, ite_false] using hx

theorem correct_scoped (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (answer : List Bool → List Bool) (own : ∀ q, IntegralMixedValueFactorScopedBits.Selected P F q → answer q = IntegralMixedValueFactorValue.value P F q) :
    Correct (machine P a F h k hd) answer (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    have hs : Selected P F q := of_decide_eq_true hq
    have hk := kernel_selected P F g q hs
    have he := replies_prepared_scoped P F g answer own q hs
    exact (IntegralMixedValueCoefficientNative.value_at P F g answer _ hk.1 he).trans
      (raw_value P F g q hs)
  · intro q hq hp
    have hs : Selected P F q := of_decide_eq_true hq
    have hk := kernel_selected P F g q hs
    have hl : IntegralMixedValueCoefficientTasks.Labels P F (IntegralMixedRawKindBits.prepare P F q) := of_decide_eq_true hp
    have he := replies_prepared_scoped P F g answer own q hs hl
    change (answer (IntegralMixedValueCoefficientTasks.query P F (IntegralMixedRawKindBits.prepare P F q))).length ≤ replyWidth P q
    rw [he, IntegralMixedValueCoefficientValue.child_value P F g _ hk.1 hl]
    let : NeZero (modulus P (IntegralMixedRawKindBits.prepare P F q)) := ⟨modulus_ne_zero P _⟩
    exact (IntegralMixedValueCoefficientValue.value_length P F _).trans_eq
      (congrArg Nat.size (IntegralMixedRawKindBits.prepare_modulus P F q))
  · intro q c budget hq hc
    have hs : Selected P F q := of_decide_eq_true hq
    have he := (Controller.prepare_requests_iff (IntegralMixedValueCoefficientNative.program P F).controller
      (IntegralMixedRawKindBits.prepare P F) answer budget q c).mp hc
    have hchild := ((SingleCall.Program.requests_iff (IntegralMixedValueCoefficientNative.program P F)
      answer (fun _ => budget q) (IntegralMixedRawKindBits.prepare P F q) c).mp he).2
    change c = IntegralMixedValueCoefficientTasks.query P F (IntegralMixedRawKindBits.prepare P F q) at hchild
    rw [hchild]
    exact IntegralMixedRawKindBits.prepare_frame P F q _ hs.2.1 hs.2.2.1
      (IntegralMixedValueCoefficientTasks.query_frame P F _ (IntegralMixedRawKindBits.prepare_routine P F q)
        (IntegralMixedRawKindBits.prepare_phase P F q))

end LeanCanny.Algebra.IntegralMixedPreparedValueNative

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLeafReplyMatching
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeValidBranch
/-! # Valid-current physical leaf machines for a total zero-extended dispatcher

Current derivative replies are required only at the guarded actual child.
No reply identity at an invalid birth is needed. The raw leaf APIs remain
available separately for source models that intentionally evaluate all words.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def guardedOriginalMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine :=
  ofSingleCall (originalProgram P F) (original_certificates P a F h ha)
    (selectedValid P .originalCoefficient) (selectedValid_FP P a .originalCoefficient) (original P F) (fun _ => 0) (UnaryFn.const 0)

theorem guardedOriginal_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (reply : List Bool → List Bool) :
    Correct (guardedOriginalMachine P a F h ha) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofSingleCall_correct
  · intro q _; rfl
  · intro q _ hr; cases hr
  · intro q c budget _ hc
    obtain ⟨hr, _⟩ := ((originalProgram P F).requests_iff reply budget q c).mp hc
    cases hr

noncomputable def guardedDerivativeMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (derivativeProgram P F)
    ((derivativeProgram P F).certificates (IntegralCriticalFlatDerivativeBits.controls P a (derivativeSource P F) (derivativeAccess P a F h)))
    (derivativeInput P F) (IntegralCriticalFlatDerivativeBits.input_FP P a (derivativeSource P F) (derivativeAccess P a F h))
    (selectedValid P .derivativeCoefficient) (selectedValid_FP P a .derivativeCoefficient)
    (IntegralMixedPhysicalCoefficientBits.derivative P F) (replyBound P) (replyBound_unary P a)

abbrev GuardedOriginalMatches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ q, selectedValid P .originalCoefficient q = true → reply q = original P F q

theorem guarded_derivative_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool)
    (he : GuardedOriginalMatches P F reply) (q : List Bool) (hq : selectedValid P .derivativeCoefficient q = true) :
    DerivativeRepliesAt P F reply q := by
  intro _
  apply he
  apply (selectedValid_iff P .originalCoefficient _).mpr
  have HQ := (selectedValid_iff P .derivativeCoefficient q).mp hq
  constructor
  · let z := IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)
    have HO : IntegralDerivativeBits.original z = q :=
      (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans
        (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
    change birth P (IntegralCriticalFlatDerivativeQuery.writer P z) < P.cap (RankedHistoryTask.root (IntegralCriticalFlatDerivativeQuery.writer P z))
    rw [IntegralCriticalFlatDerivativeQuery.writer_birth, IntegralCriticalFlatDerivativeQuery.writer_root, HO]
    exact HQ.1
  · exact (selected_iff P .originalCoefficient _).mp (derivative_original_selected P F q
      ((selected_iff P .derivativeCoefficient q).mpr HQ.2))
theorem guardedDerivative_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .derivativeCoefficient q = true → DerivativeRepliesAt P F reply q) :
    Correct (guardedDerivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  classical
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact derivative_value_at P a F h g reply q (he q hq)
  · intro q hq hr
    have HH : IntegralDerivativeBits.flatRequest (derivativeSource P F) (derivativeInput P F q) := of_decide_eq_true hr
    have HC := he q hq HH
    have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)) = q :=
      (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
    have HM : modulus P (IntegralCriticalFlatDerivativeQuery.writer P
        (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q))) = modulus P q :=
      (IntegralCriticalFlatDerivativeQuery.writer_modulus P _).trans (congrArg (modulus P) HO)
    change (reply (IntegralCriticalFlatDerivativeQuery.writer P
      (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)))).length ≤ replyBound P q
    rw [HC]
    exact (original_length P F _).trans_eq (congrArg Nat.size HM)
  · intro q c budget hq hc
    exact derivative_requests_frame P (derivativeSource P F) reply budget q c
      ((selectedValid_iff P .derivativeCoefficient q).mp hq).2.2 hc

theorem guardedDerivative_correct_of_original (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : GuardedOriginalMatches P F reply) :
    Correct (guardedDerivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  guardedDerivative_correct P a F h g reply (guarded_derivative_replies P F reply he)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits

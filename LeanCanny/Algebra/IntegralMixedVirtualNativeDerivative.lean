/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualDerivativeTransport
public import LeanCanny.Algebra.IntegralMixedVirtualNativeHeight
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
public import LeanCanny.Computation.NativePreparedSingleCallBranch
/-! # Native virtual derivative coefficients with a guarded bumped original leaf -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev derivativeSource (P : Parameters) (F : Family) := IntegralMixedVirtualCoefficientBits.source P F
noncomputable abbrev derivativeAccess (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) := IntegralMixedVirtualCoefficientBits.access P a F h
noncomputable abbrev derivativeProgram (P : Parameters) (F : Family) := IntegralCriticalFlatDerivativeBits.program P (derivativeSource P F)
noncomputable abbrev derivativeInput (P : Parameters) (F : Family) := IntegralCriticalFlatDerivativeBits.input P (derivativeSource P F)

noncomputable def derivativeMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (derivativeProgram P F)
    ((derivativeProgram P F).certificates (IntegralCriticalFlatDerivativeBits.controls P a (derivativeSource P F) (derivativeAccess P a F h)))
    (derivativeInput P F) (IntegralCriticalFlatDerivativeBits.input_FP P a (derivativeSource P F) (derivativeAccess P a F h))
    (selectedValid P .derivativeCoefficient) (selectedValid_FP P a .derivativeCoefficient)
    (IntegralMixedVirtualCoefficientBits.derivative P F) (heightBound P) (heightBound_unary P a)

abbrev DerivativeRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  IntegralDerivativeBits.flatRequest (derivativeSource P F) (derivativeInput P F q) →
    reply (IntegralCriticalFlatDerivativeQuery.writer P
      (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q))) =
        original P F (IntegralCriticalFlatDerivativeQuery.writer P
          (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)))

theorem derivative_frame (P : Parameters) (z : List Bool) (hp : isPhase .derivativeCoefficient (IntegralDerivativeBits.original z)) :
    IntegralMixedRoutineTaskBits.Frame P (IntegralDerivativeBits.original z) (IntegralCriticalFlatDerivativeQuery.writer P z) := by
  apply IntegralMixedMatrixFrames.frame_of_ordinary
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatDerivativeQuery.writer_other P z .slot14 (by decide) (by decide) (by decide)]
  · exact ⟨IntegralCriticalFlatDerivativeQuery.writer_root P z, IntegralCriticalFlatDerivativeQuery.writer_length P z,
      IntegralCriticalFlatDerivativeQuery.writer_lower_rank P z hp⟩

theorem derivative_requests_frame (P : Parameters) (S : IntegralDerivativeBits.Source)
    (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .derivativeCoefficient q)
    (hc : ((IntegralCriticalFlatDerivativeBits.program P S).controller.prepare (IntegralCriticalFlatDerivativeBits.input P S)).Requests reply budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  let C := IntegralCriticalFlatDerivativeBits.program P S
  let I := IntegralCriticalFlatDerivativeBits.input P S
  have H0 : C.controller.Requests reply (fun _ => budget q) (I q) c :=
    (RecursiveController.Controller.prepare_requests_iff C.controller I reply budget q c).mp hc
  have H1 := (C.requests_iff reply (fun _ => budget q) (I q) c).mp H0
  have HQ : C.query (I q) = IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery S (I q)) := rfl
  have HE := H1.2.trans HQ
  have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery S (I q)) = q :=
    (IntegralDerivativeBits.flatQuery_original S _).trans (IntegralCriticalFlatDerivativeBits.input_original P S q)
  have HP := Eq.mpr (congrArg (isPhase .derivativeCoefficient) HO) hp
  have HF := derivative_frame P (IntegralDerivativeBits.flatQuery S (I q)) HP
  have HFQ := Eq.mp (congrArg (fun parent => IntegralMixedRoutineTaskBits.Frame P parent
    (IntegralCriticalFlatDerivativeQuery.writer P (IntegralDerivativeBits.flatQuery S (I q)))) HO) HF
  exact Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) HE) HFQ

theorem original_length (P : Parameters) (F : Family) (q : List Bool) : (original P F q).length ≤ (modulus P q).size := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  rw [IntegralMixedVirtualCoefficientBits.original_snapshot]
  unfold IntegralMixedVirtualCoefficientBits.originalAt
  exact residueBits_length_le _ _

theorem derivative_value_at (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (he : DerivativeRepliesAt P F reply q) :
    (derivativeProgram P F).value reply (derivativeInput P F q) = IntegralMixedVirtualCoefficientBits.derivative P F q := by
  apply Eq.trans (IntegralDerivativeBits.program_value_at (derivativeSource P F) (derivativeAccess P a F h)
    (IntegralCriticalFlatDerivativeQuery.writer P) reply (derivativeInput P F q) ?_)
    (IntegralMixedVirtualCoefficientBits.derivative_packet P a F h q)
  intro hr
  exact (he hr).trans (IntegralMixedVirtualCoefficientBits.bumped_child P a F h g q hv)

theorem derivative_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .derivativeCoefficient q = true → DerivativeRepliesAt P F reply q) :
    Correct (derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  classical
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact derivative_value_at P a F h g reply q ((selectedValid_iff P .derivativeCoefficient q).mp hq).1 (he q hq)
  · intro q hq hr
    have HH : IntegralDerivativeBits.flatRequest (derivativeSource P F) (derivativeInput P F q) := of_decide_eq_true hr
    have HC := he q hq HH
    have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)) = q :=
      (IntegralDerivativeBits.flatQuery_original (derivativeSource P F) _).trans (IntegralCriticalFlatDerivativeBits.input_original P (derivativeSource P F) q)
    have HM : modulus P (IntegralCriticalFlatDerivativeQuery.writer P
        (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q))) = modulus P q :=
      (IntegralCriticalFlatDerivativeQuery.writer_modulus P _).trans (congrArg (modulus P) HO)
    change (reply (IntegralCriticalFlatDerivativeQuery.writer P
      (IntegralDerivativeBits.flatQuery (derivativeSource P F) (derivativeInput P F q)))).length ≤ heightBound P q
    rw [HC]
    exact (original_length P F _).trans_eq (congrArg Nat.size HM)
  · intro q c budget hq hc
    exact derivative_requests_frame P (derivativeSource P F) reply budget q c
      ((selectedValid_iff P .derivativeCoefficient q).mp hq).2.2 hc
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits

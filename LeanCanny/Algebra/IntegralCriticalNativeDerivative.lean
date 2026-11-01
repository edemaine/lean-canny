/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativePreparedSingleCallBranch
public import LeanCanny.Algebra.IntegralCriticalNativeLowerFrames
/-! # Native derivative branch with only its actual bumped coefficient reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeDerivativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank

noncomputable abbrev source (F : Scripts) := IntegralCriticalActualDerivativeTransport.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalActualDerivativeTransport.access F h
noncomputable abbrev program (F : Scripts) := IntegralCriticalFlatDerivativeBits.program F.toParameters (source F)
noncomputable abbrev input (F : Scripts) := IntegralCriticalFlatDerivativeBits.input F.toParameters (source F)

theorem certificates (F : Scripts) (h : Controls F) :
    (program F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F).certificates (IntegralCriticalFlatDerivativeBits.controls F.toParameters h.task.toAccess (source F) (access F h))

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofPreparedSingleCall (program F) (certificates F h) (input F)
    (IntegralCriticalFlatDerivativeBits.input_FP F.toParameters h.task.toAccess (source F) (access F h))
    (selected F .derivativeCoefficient) (selected_FP F h .derivativeCoefficient)
    (IntegralCriticalActualCoefficientModel.derivative F) (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem requests_frame_source (F : Scripts) (S : IntegralDerivativeBits.Source)
    (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .derivativeCoefficient q)
    (hc : ((IntegralCriticalFlatDerivativeBits.program F.toParameters S).controller.prepare
      (IntegralCriticalFlatDerivativeBits.input F.toParameters S)).Requests reply budget q c) : Frame F q c := by
  let P := IntegralCriticalFlatDerivativeBits.program F.toParameters S
  let I := IntegralCriticalFlatDerivativeBits.input F.toParameters S
  have H0 : P.controller.Requests reply (fun _ => budget q) (I q) c :=
    (RecursiveController.Controller.prepare_requests_iff P.controller I reply budget q c).mp hc
  have H1 := (P.requests_iff reply (fun _ => budget q) (I q) c).mp H0
  have HQ : P.query (I q) = IntegralCriticalFlatDerivativeQuery.writer F.toParameters
      (IntegralDerivativeBits.flatQuery S (I q)) := rfl
  have HE : c = IntegralCriticalFlatDerivativeQuery.writer F.toParameters (IntegralDerivativeBits.flatQuery S (I q)) :=
    H1.2.trans HQ
  have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery S (I q)) = q :=
    (IntegralDerivativeBits.flatQuery_original S _).trans
      (IntegralCriticalFlatDerivativeBits.input_original F.toParameters S q)
  have HP := Eq.mpr (congrArg (isPhase .derivativeCoefficient) HO) hp
  have HF := frame_derivative F (IntegralDerivativeBits.flatQuery S
    (IntegralCriticalFlatDerivativeBits.input F.toParameters S q)) HP
  have HFQ := Eq.mp (congrArg (fun p => Frame F p (IntegralCriticalFlatDerivativeQuery.writer F.toParameters
    (IntegralDerivativeBits.flatQuery S (IntegralCriticalFlatDerivativeBits.input F.toParameters S q)))) HO) HF
  exact Eq.mpr (congrArg (Frame F q) HE) HFQ

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .derivativeCoefficient q)
    (hc : ((program F).controller.prepare (input F)).Requests reply budget q c) : Frame F q c :=
  requests_frame_source F (source F) reply budget q c hp hc

theorem value_at (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) (input F q) = IntegralCriticalActualCoefficientModel.derivative F q := by
  apply Eq.trans (IntegralDerivativeBits.program_value_at (source F) (access F h)
    (IntegralCriticalFlatDerivativeQuery.writer F.toParameters) (answer F x) (input F q) ?_)
    (IntegralCriticalActualDerivativeTransport.derivative_packet F h q)
  intro _
  have HO : IntegralDerivativeBits.original (IntegralDerivativeBits.flatQuery (source F) (input F q)) = q :=
    (IntegralDerivativeBits.flatQuery_original (source F) _).trans
      (IntegralCriticalFlatDerivativeBits.input_original F.toParameters (source F) q)
  exact (matches_derivative F x hm _ (by rw [HO]; exact hv)).trans
    (IntegralCriticalActualDerivativeTransport.bumped_child F h q hv)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (machine F h) (answer F x) (Frame F) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact value_at F h x hm q ((selected_iff F .derivativeCoefficient q).mp hq).1
  · intro q hq hr
    have HC : ((program F).controller.prepare (input F)).Requests (answer F x) (fun _ => 1) q
        ((program F).query (input F q)) :=
      (RecursiveController.Controller.prepare_requests_iff (program F).controller (input F) (answer F x) (fun _ => 1) q _).mpr
        (((program F).requests_iff (answer F x) (fun _ => 1) (input F q) _).mpr ⟨hr, rfl⟩)
    exact IntegralCriticalNativeBranchBits.answer_length F x q _
      (requests_frame F (answer F x) (fun _ => 1) q _ ((selected_iff F .derivativeCoefficient q).mp hq).2 HC).1
  · intro q c budget hq hc
    exact requests_frame F (answer F x) budget q c ((selected_iff F .derivativeCoefficient q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeDerivativeBits

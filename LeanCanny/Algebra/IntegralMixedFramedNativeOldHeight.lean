/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightPassBounds
public import LeanCanny.Algebra.IntegralMixedFramedOldHeightValue
public import LeanCanny.Computation.RecursiveFoldPostprocess
/-! # Native mixed scalar0/2 with literal bank semantics and earlier producer requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits NativeControllerBranch
open IntegralMixedOldHeightBits (request request_FP)
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def post (P : Parameters) (z : List Bool) := if request P (pairFst z) then pairSnd z else []

theorem post_FP (P : Parameters) (a : Access P) : post P ∈ FP :=
  ((request_FP P a).comp pairFst_mem_FP).ite_mem_FP pairSnd_mem_FP (constFn_mem_FP [])

noncomputable def controller (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) :=
  (passProgram P D F R).postController (post P)

theorem program_count (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) :
    (passProgram P D F R).count = passCount P := rfl

attribute [local irreducible] passProgram passScalars IntegralMixedFramedOldHeightBits.value cofactor companionInteger

theorem certificates (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) :
    (controller P D F R).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  (passProgram P D F R).post_certificates (passCertificates P a D F R hr) _ (SpaceFunction.ofFP _ (post_FP P a))

theorem post_value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (he : PassRepliesAt P D F R reply q) :
    post P (pair q ((passProgram P D F R).value reply q)) = value P D F q := by
  simp only [post, pairFst_pair, pairSnd_pair]
  by_cases HQ : request P q
  · rw [ite_eq_left HQ, pass_value P D F R reply q he, pass_cofactor P D F R q HQ]
    simpa only [Int.cast_mul] using (value_request P D F R q HQ).symm
  · rw [ite_eq_right HQ]
    exact (value_not_request P D F R q HQ).symm

theorem output_when_halted (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (t : ℕ) (he : PassRepliesAt P D F R reply q)
    (hh : (controller P D F R).halted (((controller P D F R).reference reply)^[t] ((controller P D F R).initial q)) = true) :
    (controller P D F R).output (((controller P D F R).reference reply)^[t] ((controller P D F R).initial q)) = value P D F q :=
  ((passProgram P D F R).post_output_when_halted (post P) reply q t hh).trans (post_value P D F R reply q he)

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .clearedHeight q)

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and (isPhase_FP .clearedHeight))).flag_mem_FP

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .clearedHeight q := by
  simp only [selected, decide_eq_true_eq]

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := controller P D F R
  certificates := certificates P a D F R hr
  selected := selected P
  selected_FP := selected_FP P a
  model := value P D F
  clock := passCount P
  clock_binary := BinaryFn.ofUnary (passCount_unary P a)
  stateBound := passStateBound P
  stateBound_unary := passStateBound_unary P a

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (F : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) (reply : List Bool → List Bool)
    (he : ∀ q, selected P q = true → PassRepliesAt P D F R reply q) :
    Correct (machine P a D F R hr) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    simpa only [machine, controller, program_count] using (passProgram P D F R).post_halted_after (post P) reply q
  · intro q t hq hh
    exact output_when_halted P D F R reply q t (he q hq) hh
  · intro q t hq
    exact pass_state_length P D F R reply q (he q hq) t
  · intro q c budget _ hc
    have HC : (passProgram P D F R).controller.Requests reply budget q c :=
      ((passProgram P D F R).post_requests (post P) reply budget q c).mp hc
    exact pass_requests_frame P D F R reply q c budget HC

end LeanCanny.Algebra.IntegralMixedFramedNativeOldHeightBits

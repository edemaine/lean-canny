/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightPost
public import LeanCanny.Computation.RecursiveFoldPostprocess
/-! # Native mixed scalar0/4 from current bank/reference replies and original cells -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedScalarCellsBits (Primitive)
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) :=
  (IntegralMixedFramedHeightTablePassBits.program P R).postController (IntegralMixedFramedHeightPostBits.post P D J)

noncomputable def model (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  IntegralMixedFramedHeightPostBits.post P D J (pair q (IntegralMixedFramedHeightTablePassBits.value P D J q))

theorem program_count (P : Parameters) (R : Routing) :
    (IntegralMixedFramedHeightTablePassBits.program P R).count =
      fun q => IntegralMixedFramedHeightTablePassBits.count P q * IntegralMixedFramedHeightTablePassBits.width P q := rfl

attribute [local irreducible] IntegralMixedFramedHeightTablePassBits.program model

theorem certificates (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D J) :
    (controller P D J R).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  (IntegralMixedFramedHeightTablePassBits.program P R).post_certificates (IntegralMixedFramedHeightTablePassBits.certificates P a R hr)
    _ (IntegralMixedFramedHeightPostBits.post_space P a D J hp)

theorem output_when_halted (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (t : ℕ) (he : IntegralMixedFramedHeightTablePassBits.RepliesAt P D J R reply q)
    (hh : (controller P D J R).halted (((controller P D J R).reference reply)^[t] ((controller P D J R).initial q)) = true) :
    (controller P D J R).output (((controller P D J R).reference reply)^[t] ((controller P D J R).initial q)) = model P D J q := by
  have H := (IntegralMixedFramedHeightTablePassBits.program P R).post_output_when_halted (IntegralMixedFramedHeightPostBits.post P D J) reply q t hh
  refine H.trans ?_
  rw [IntegralMixedFramedHeightTablePassBits.value_at P D J R reply q he]
  unfold model
  rfl

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .factorPower q ∧
    1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase .factorPower q ∧
      1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by simp only [selected, decide_eq_true_eq]

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and
      ((isPhase_FP .factorPower).and (((BinaryFn.const 1).le (get_binary P a .slot15)).and
        ((get_binary P a .slot15).le (BinaryFn.const 4)))))).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D J) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := controller P D J R
  certificates := certificates P a D J R hr hp
  selected := selected P
  selected_FP := selected_FP P a
  model := model P D J
  clock q := IntegralMixedFramedHeightTablePassBits.count P q * IntegralMixedFramedHeightTablePassBits.width P q
  clock_binary := BinaryFn.ofUnary ((IntegralMixedFramedHeightTablePassBits.count_unary P a).mul (IntegralMixedFramedHeightTablePassBits.width_unary P a))
  stateBound := FixedWidthVectorPass.stateBound (IntegralMixedFramedHeightTablePassBits.count P) (IntegralMixedFramedHeightTablePassBits.width P)
  stateBound_unary := FixedWidthVectorPass.stateBound_unary _ _ (IntegralMixedFramedHeightTablePassBits.count_unary P a) (IntegralMixedFramedHeightTablePassBits.width_unary P a)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D J) (reply : List Bool → List Bool)
    (he : ∀ q, selected P q = true → IntegralMixedFramedHeightTablePassBits.RepliesAt P D J R reply q) :
    Correct (machine P a D J R hr hp) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    simpa only [machine, controller, program_count] using
      (IntegralMixedFramedHeightTablePassBits.program P R).post_halted_after (IntegralMixedFramedHeightPostBits.post P D J) reply q
  · intro q t hq hh
    exact output_when_halted P D J R reply q t (he q hq) hh
  · intro q t _
    have H := FixedWidthVectorPass.state_length (IntegralMixedFramedHeightTablePassBits.count P) (IntegralMixedFramedHeightTablePassBits.width P)
      (IntegralMixedFramedHeightTablePassBits.task P R) reply q t
    simpa only [machine, controller, RecursiveFold.Program.post_reference, RecursiveFold.Program.post_initial,
      IntegralMixedFramedHeightTablePassBits.program] using H
  · intro q c budget hq hc
    have HQ := (selected_iff P q).mp hq
    have HC := ((IntegralMixedFramedHeightTablePassBits.program P R).post_requests (IntegralMixedFramedHeightPostBits.post P D J) reply budget q c).mp hc
    exact IntegralMixedFramedHeightTablePassBits.requests_frame P D J R reply q c budget HQ.2.1 HQ.2.2.1 HC

end LeanCanny.Algebra.IntegralMixedFramedNativeHeightBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightPost
public import LeanCanny.Computation.RecursiveFoldPostprocess
/-! # Native mixed scalar0/4 from current bank/reference replies and original cells -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNativeHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedHeightCellsBits (Primitive)
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing) :=
  (IntegralMixedHeightTablePassBits.program P R).postController (IntegralMixedHeightPostBits.post P D)

noncomputable def model (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  IntegralMixedHeightPostBits.post P D (pair q (IntegralMixedHeightTablePassBits.value P D q))

theorem program_count (P : Parameters) (R : Routing) :
    (IntegralMixedHeightTablePassBits.program P R).count =
      fun q => IntegralMixedHeightTablePassBits.count P q * IntegralMixedHeightTablePassBits.width P q := rfl

attribute [local irreducible] IntegralMixedHeightTablePassBits.program model

theorem certificates (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D) :
    (controller P D R).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  (IntegralMixedHeightTablePassBits.program P R).post_certificates (IntegralMixedHeightTablePassBits.certificates P a R hr)
    _ (IntegralMixedHeightPostBits.post_space P a D hp)

theorem output_when_halted (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (R : Routing)
    (reply : List Bool → List Bool) (q : List Bool) (t : ℕ) (he : IntegralMixedHeightTablePassBits.RepliesAt P D R reply q)
    (hh : (controller P D R).halted (((controller P D R).reference reply)^[t] ((controller P D R).initial q)) = true) :
    (controller P D R).output (((controller P D R).reference reply)^[t] ((controller P D R).initial q)) = model P D q := by
  have H := (IntegralMixedHeightTablePassBits.program P R).post_output_when_halted (IntegralMixedHeightPostBits.post P D) reply q t hh
  refine H.trans ?_
  rw [IntegralMixedHeightTablePassBits.value_at P D R reply q he]
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

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := controller P D R
  certificates := certificates P a D R hr hp
  selected := selected P
  selected_FP := selected_FP P a
  model := model P D
  clock q := IntegralMixedHeightTablePassBits.count P q * IntegralMixedHeightTablePassBits.width P q
  clock_binary := BinaryFn.ofUnary ((IntegralMixedHeightTablePassBits.count_unary P a).mul (IntegralMixedHeightTablePassBits.width_unary P a))
  stateBound := FixedWidthVectorPass.stateBound (IntegralMixedHeightTablePassBits.count P) (IntegralMixedHeightTablePassBits.width P)
  stateBound_unary := FixedWidthVectorPass.stateBound_unary _ _ (IntegralMixedHeightTablePassBits.count_unary P a) (IntegralMixedHeightTablePassBits.width_unary P a)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (R : Routing) (hr : RoutingAccess R) (hp : Primitive P D) (reply : List Bool → List Bool)
    (he : ∀ q, selected P q = true → IntegralMixedHeightTablePassBits.RepliesAt P D R reply q) :
    Correct (machine P a D R hr hp) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    simpa only [machine, controller, program_count] using
      (IntegralMixedHeightTablePassBits.program P R).post_halted_after (IntegralMixedHeightPostBits.post P D) reply q
  · intro q t hq hh
    exact output_when_halted P D R reply q t (he q hq) hh
  · intro q t _
    have H := FixedWidthVectorPass.state_length (IntegralMixedHeightTablePassBits.count P) (IntegralMixedHeightTablePassBits.width P)
      (IntegralMixedHeightTablePassBits.task P R) reply q t
    simpa only [machine, controller, RecursiveFold.Program.post_reference, RecursiveFold.Program.post_initial,
      IntegralMixedHeightTablePassBits.program] using H
  · intro q c budget hq hc
    have HQ := (selected_iff P q).mp hq
    have HC := ((IntegralMixedHeightTablePassBits.program P R).post_requests (IntegralMixedHeightPostBits.post P D) reply budget q c).mp hc
    exact IntegralMixedHeightTablePassBits.requests_frame P D R reply q c budget HQ.2.1 HQ.2.2.1 HC

end LeanCanny.Algebra.IntegralMixedNativeHeightBits

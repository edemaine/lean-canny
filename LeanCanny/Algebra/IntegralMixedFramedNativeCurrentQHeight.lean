/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQHeightPost
public import LeanCanny.Algebra.IntegralMixedFramedHeightCurrentReplies
/-! # Current-Q slope restoration keeps the existing charged child schedule

Only output postprocessing changes. The table, clocks, state size, child words,
and decreasing ranks are the literal existing earlier-leading/old-height pass.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeCurrentQHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedCurrentQHeightBits (Controls post post_space post_table)
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess)
open IntegralMixedFramedNativeHeightBits (selected selected_iff selected_FP program_count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) (h : Controls P D J) :=
  (IntegralMixedFramedHeightTablePassBits.program P R).postController (post P D J h)

attribute [local irreducible] IntegralMixedFramedHeightTablePassBits.program IntegralMixedFramedNativeHeightBits.model

theorem certificates (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) (hr : RoutingAccess R) (h : Controls P D J) :
    (controller P D J R h).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  (IntegralMixedFramedHeightTablePassBits.program P R).post_certificates (IntegralMixedFramedHeightTablePassBits.certificates P a R hr)
    _ (post_space P a D J h)

theorem output_when_halted (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) (h : Controls P D J)
    (reply : List Bool → List Bool) (q : List Bool) (t : ℕ) (he : IntegralMixedFramedHeightTablePassBits.RepliesAt P D J R reply q)
    (hh : (controller P D J R h).halted (((controller P D J R h).reference reply)^[t] ((controller P D J R h).initial q))=true) :
    (controller P D J R h).output (((controller P D J R h).reference reply)^[t] ((controller P D J R h).initial q))=
      IntegralMixedFramedNativeHeightBits.model P D J q := by
  have H := (IntegralMixedFramedHeightTablePassBits.program P R).post_output_when_halted (post P D J h) reply q t hh
  refine H.trans ?_
  rw [IntegralMixedFramedHeightTablePassBits.value_at P D J R reply q he]
  exact post_table P D J h q

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) (hr : RoutingAccess R) (h : Controls P D J) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := controller P D J R h
  certificates := certificates P a D J R hr h
  selected := selected P
  selected_FP := selected_FP P a
  model := IntegralMixedFramedNativeHeightBits.model P D J
  clock q := IntegralMixedFramedHeightTablePassBits.count P q * IntegralMixedFramedHeightTablePassBits.width P q
  clock_binary := BinaryFn.ofUnary ((IntegralMixedFramedHeightTablePassBits.count_unary P a).mul (IntegralMixedFramedHeightTablePassBits.width_unary P a))
  stateBound := FixedWidthVectorPass.stateBound (IntegralMixedFramedHeightTablePassBits.count P) (IntegralMixedFramedHeightTablePassBits.width P)
  stateBound_unary := FixedWidthVectorPass.stateBound_unary _ _ (IntegralMixedFramedHeightTablePassBits.count_unary P a) (IntegralMixedFramedHeightTablePassBits.width_unary P a)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (R : Routing) (hr : RoutingAccess R) (h : Controls P D J)
    (reply : List Bool → List Bool) (he : ∀ q,selected P q=true → IntegralMixedFramedHeightTablePassBits.RepliesAt P D J R reply q) :
    Correct (machine P a D J R hr h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    simpa only [machine,controller,program_count] using
      (IntegralMixedFramedHeightTablePassBits.program P R).post_halted_after (post P D J h) reply q
  · intro q t hq hh
    exact output_when_halted P D J R h reply q t (he q hq) hh
  · intro q t _
    have H := FixedWidthVectorPass.state_length (IntegralMixedFramedHeightTablePassBits.count P) (IntegralMixedFramedHeightTablePassBits.width P)
      (IntegralMixedFramedHeightTablePassBits.task P R) reply q t
    simpa only [machine,controller,RecursiveFold.Program.post_reference,RecursiveFold.Program.post_initial,
      IntegralMixedFramedHeightTablePassBits.program] using H
  · intro q c budget hq hc
    have HQ := (selected_iff P q).mp hq
    have HC := ((IntegralMixedFramedHeightTablePassBits.program P R).post_requests (post P D J h) reply budget q c).mp hc
    exact IntegralMixedFramedHeightTablePassBits.requests_frame P D J R reply q c budget HQ.2.1 HQ.2.2.1 HC

theorem correct_of_current (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (T : IntegralMixedHeaderTablesBits.Tables)
    (ht : IntegralMixedHeaderTablesBits.Access T) (hr : IntegralMixedFramedHeaderBits.Represents P D J T)
    (h : Controls P D J) (reply : List Bool → List Bool)
    (hp : IntegralMixedFramedProducerActualBits.Matches P D J reply) (hm : IntegralMixedFramedHeightCurrentBits.Matches P D J reply) :
    Correct (machine P a D J (IntegralMixedFramedHeaderBits.routing P D)
      (IntegralMixedFramedHeaderBits.routingAccess P a D J T ht hr) h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D J _ (IntegralMixedFramedHeaderBits.routingAccess P a D J T ht hr) h reply
    (fun q hq => IntegralMixedFramedHeightCurrentBits.replies P D J reply hp hm q hq)
end LeanCanny.Algebra.IntegralMixedFramedNativeCurrentQHeightBits

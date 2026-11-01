/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
public import LeanCanny.Algebra.IntegralMixedVirtualDenominatorPost
public import LeanCanny.Algebra.IntegralMixedOldBankProvenance
public import LeanCanny.Computation.RecursiveFoldPostprocess
/-! # Native scalar0/1 denominator with actual earlier-producer requests

The internal fold computes the old bank product. Its output combines
that residue with the original affine rule-scale cells to obtain the
literal virtual-source denominator. Only those immutable integer cells
are charged primitive reads; no state or retained-leading evaluator is
assumed. Every recursive child has strictly earlier scalar-prefix birth.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open IntegralMixedOldBankCofactorBits (Routing RoutingAccess RepliesAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def program (P : Parameters) (F : Family) (R : Routing) : RecursiveFold.Program :=
  IntegralMixedOldBankCofactorBits.program P F (IntegralMixedOldBankCofactorBits.count P F) R

theorem program_count (P : Parameters) (F : Family) (R : Routing) :
    (program P F R).count = IntegralMixedOldBankCofactorBits.count P F := rfl

attribute [local irreducible] program

noncomputable def controller (P : Parameters) (F : Family) (R : Routing) :
    RecursiveController.Controller (List Bool) RecursiveFold.State :=
  (program P F R).postController (IntegralMixedVirtualDenominatorPostBits.post P F)

abbrev Primitive (P : Parameters) (F : Family) := SpaceFunction (IntegralMixedVirtualDenominatorPostBits.rawScaleReader P F)

theorem certificates (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R) (hp : Primitive P F) :
    (controller P F R).Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) := by
  have HC : (program P F R).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) := by
    unfold program
    exact IntegralMixedOldBankCofactorBits.certificates P a F g (IntegralMixedOldBankCofactorBits.count P F)
      (BinaryFn.ofUnary (IntegralMixedOldBankCofactorBits.count_unary P a F g)) R hr
  exact (program P F R).post_certificates HC _ (IntegralMixedVirtualDenominatorPostBits.post_space P a F h hp)

theorem reference_eq (P : Parameters) (F : Family) (R : Routing) (reply : List Bool → List Bool) :
    (controller P F R).reference reply = (program P F R).controller.reference reply :=
  (program P F R).post_reference _ reply

theorem requests_iff (P : Parameters) (F : Family) (R : Routing) (reply : List Bool → List Bool)
    (budget : List Bool → ℕ) (q c : List Bool) : (controller P F R).Requests reply budget q c ↔
      (program P F R).controller.Requests reply budget q c :=
  (program P F R).post_requests _ reply budget q c

theorem output_when_halted (P : Parameters) (F : Family) (R : Routing) (reply : List Bool → List Bool)
    (q : List Bool) (t : ℕ) (he : RepliesAt P F R reply q)
    (hh : (controller P F R).halted (((controller P F R).reference reply)^[t] ((controller P F R).initial q)) = true) :
    (controller P F R).output (((controller P F R).reference reply)^[t] ((controller P F R).initial q)) =
      IntegralMixedVirtualDenominatorBits.value P F q := by
  have H := (program P F R).post_output_when_halted (IntegralMixedVirtualDenominatorPostBits.post P F) reply q t hh
  refine H.trans ?_
  unfold program
  rw [IntegralMixedOldBankCofactorBits.value_at P F _ R reply q he, IntegralMixedVirtualDenominatorPostBits.post_full]

noncomputable def selected (P : Parameters) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧
    isPhase .derivativeCoefficient q ∧ IntegralMixedVirtualContextBits.context P q)

theorem selected_FP (P : Parameters) (a : Access P) : (fun q => [selected P q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and
      ((isPhase_FP .derivativeCoefficient).and (IntegralMixedVirtualContextBits.context_FP P a)))).flag_mem_FP

theorem selected_iff (P : Parameters) (q : List Bool) : selected P q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧
      isPhase .derivativeCoefficient q ∧ IntegralMixedVirtualContextBits.context P q := by
  simp only [selected, decide_eq_true_eq]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R) (hp : Primitive P F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := controller P F R
  certificates := certificates P a F h g R hr hp
  selected := selected P
  selected_FP := selected_FP P a
  model := IntegralMixedVirtualDenominatorBits.value P F
  clock := IntegralMixedOldBankCofactorBits.count P F
  clock_binary := BinaryFn.ofUnary (IntegralMixedOldBankCofactorBits.count_unary P a F g)
  stateBound := IntegralMixedOldBankCofactorBits.stateBound P F
  stateBound_unary := IntegralMixedOldBankCofactorBits.stateBound_unary P a F g

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R) (hp : Primitive P F)
    (reply : List Bool → List Bool) (he : ∀ q, selected P q = true → RepliesAt P F R reply q) :
    Correct (machine P a F h g R hr hp) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    simpa only [machine, controller, program_count] using
      (program P F R).post_halted_after (IntegralMixedVirtualDenominatorPostBits.post P F) reply q
  · intro q t hq hh
    exact output_when_halted P F R reply q t (he q hq) hh
  · intro q t hq
    simp only [machine, controller, RecursiveFold.Program.post_reference, RecursiveFold.Program.post_initial]
    unfold program
    exact IntegralMixedOldBankCofactorBits.state_length_at P F _ R reply q (he q hq) t
  · intro q c budget _ hc
    have HC := (requests_iff P F R reply budget q c).mp hc
    unfold program at HC
    exact IntegralMixedOldBankCofactorBits.requests_frame P F g _ R reply q c budget HC

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R) (hp : Primitive P F) :
    (machine P a F h g R hr hp).model = IntegralMixedVirtualDenominatorBits.value P F := rfl

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (R : Routing) (hr : RoutingAccess R) (hp : Primitive P F) :
    (machine P a F h g R hr hp).selected = selected P := rfl
end LeanCanny.Algebra.IntegralMixedVirtualContextDenominatorBits

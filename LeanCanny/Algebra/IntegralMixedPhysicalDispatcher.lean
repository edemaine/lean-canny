/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLowerModel
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperRelativeReplies
public import LeanCanny.Algebra.IntegralMixedPhysicalUpperDomain
/-! # One native arithmetic dispatcher for actual physical critical sources

Only immutable original coefficient leaves carry a SpaceFunction cost.
Scalar denominator, height, and leading answers remain charged current
requests, selected solely in physical producer context one.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits (originalScalar)
set_option backward.isDefEq.respectTransparency false

def lowerSelected (q : List Bool) : Bool := decide (phase q ≤ 16)
theorem lowerSelected_FP : (fun q => [lowerSelected q]) ∈ FP :=
  ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 16)).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine :=
  ((IntegralMixedPhysicalLowerDispatcherBits.machine P a F h ha).withGuard lowerSelected lowerSelected_FP).choose
    (IntegralMixedPhysicalUpperDispatcherBits.machine P a F h)

private theorem dispatch_selected (ns : List (PhaseNode phase)) (q : List Bool) :
    (phaseDispatch ns zero).selected q = true := by
  induction ns with
  | nil => rfl
  | cons b bs ih =>
    change (b.machine.selected q || (phaseDispatch bs zero).selected q) = true
    rw [ih, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : IntegralMixedPhysicalComponentBits.Matches P F (fun q => residueBits (x q)))
    (hc : IntegralMixedPhysicalContextLowerReplyBits.Callbacks P F (fun q => residueBits (x q)))
    (hl : IntegralMixedPhysicalUpperReplyBits.LeadingCallback P F (fun q => residueBits (x q))) :
    Correct (machine P a F h ha) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedPhysicalLowerDispatcherBits.correct P a F h ha g _
        (IntegralMixedPhysicalComponentBits.lower_matches P F _ hm) hc
    · intro q _
      exact dispatch_selected (IntegralMixedPhysicalLowerDispatcherBits.nodes P a F h ha) q
  · exact IntegralMixedPhysicalUpperReplyBits.correct P a F h g x hm hl

private theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) :
    (machine P a F h ha).model q = bif lowerSelected q then
      (IntegralMixedPhysicalLowerDispatcherBits.machine P a F h ha).model q else
      (IntegralMixedPhysicalUpperDispatcherBits.machine P a F h).model q := by
  rw [Bool.cond_eq_ite]
  rfl

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (p : Phase) (q : List Bool) (hp25 : p.code ≤ 25)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : get P .slot15 q = 1) (hp : isPhase p q) :
    (machine P a F h ha).model q = IntegralMixedPhysicalComponentBits.component P F p q := by
  rw [machine_model]
  by_cases hl : p.code ≤ 16
  · have HS : lowerSelected q = true := by
      unfold lowerSelected
      rw [hp]
      exact decide_eq_true hl
    rw [HS, Bool.cond_true, IntegralMixedPhysicalComponentBits.component_lower P F p q hl]
    exact IntegralMixedPhysicalLowerDispatcherBits.model_phase P a F h ha p q hl
      (by simp only [IntegralMixedPhysicalContextBits.selected, hv, hr, hp, hx, and_self, decide_true])
  · have HS : lowerSelected q = false := by
      unfold lowerSelected
      rw [hp]
      exact decide_eq_false hl
    rw [HS, Bool.cond_false, IntegralMixedPhysicalComponentBits.component_upper P F p q (by omega)]
    exact IntegralMixedPhysicalUpperDispatcherBits.model_phase P a F h p q (by omega) hp25 hv hr hx hp

theorem model_invalid (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hv : ¬ IntegralMixedVirtualCaps.valid P q) :
    (machine P a F h ha).model q = [] := by
  rw [machine_model, IntegralMixedPhysicalLowerDispatcherBits.model_invalid P a F h ha q hv,
    IntegralMixedPhysicalUpperDispatcherBits.model_invalid P a F h q hv]
  cases lowerSelected q <;> rfl

theorem model_other_context (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hx : get P .slot15 q ≠ 1) :
    (machine P a F h ha).model q = [] := by
  rw [machine_model, IntegralMixedPhysicalLowerDispatcherBits.model_other_context P a F h ha q hx,
    IntegralMixedPhysicalUpperDispatcherBits.model_other_context P a F h q hx]
  cases lowerSelected q <;> rfl
end LeanCanny.Algebra.IntegralMixedPhysicalDispatcherBits

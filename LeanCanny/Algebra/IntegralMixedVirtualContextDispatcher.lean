/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextLowerModelView
public import LeanCanny.Algebra.IntegralMixedVirtualContextUpperRelativeReplies
public import LeanCanny.Algebra.IntegralMixedVirtualContextUpperDomain
/-! # One native arithmetic dispatcher for actual virtual critical sources

Only immutable original coefficient leaves carry a SpaceFunction cost.
Scalar denominator, height, and leading answers remain charged current
requests, selected solely in virtual producer contexts two through four.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
open IntegralMixedVirtualNativeLowerBits (originalScalar)
set_option backward.isDefEq.respectTransparency false

def lowerSelected (q : List Bool) : Bool := decide (phase q ≤ 16)
theorem lowerSelected_FP : (fun q => [lowerSelected q]) ∈ FP :=
  ((BinaryFn.ofUnary (RankedHistoryTask.phase_unary 27)).le (BinaryFn.const 16)).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) : Machine :=
  ((IntegralMixedVirtualContextLowerDispatcherBits.machine P a F h ha).withGuard lowerSelected lowerSelected_FP).choose
    (IntegralMixedVirtualContextUpperDispatcherBits.machine P a F h)

private theorem dispatch_selected (ns : List (PhaseNode phase)) (q : List Bool) :
    (phaseDispatch ns zero).selected q = true := by
  induction ns with
  | nil => rfl
  | cons b bs ih =>
    change (b.machine.selected q || (phaseDispatch bs zero).selected q) = true
    rw [ih, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : IntegralMixedVirtualContextComponentBits.Matches P F (fun q => residueBits (x q)))
    (hc : IntegralMixedVirtualContextLowerReplyBits.Callbacks P F (fun q => residueBits (x q)))
    (hl : IntegralMixedVirtualContextUpperReplyBits.LeadingCallback P F (fun q => residueBits (x q))) :
    Correct (machine P a F h ha) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedVirtualContextLowerDispatcherBits.correct P a F h ha g _
        (IntegralMixedVirtualContextComponentBits.lower_matches P F _ hm) hc
    · intro q _
      exact dispatch_selected (IntegralMixedVirtualContextLowerDispatcherBits.nodes P a F h ha) q
  · exact IntegralMixedVirtualContextUpperReplyBits.correct P a F h g x hm hl

private theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) :
    (machine P a F h ha).model q = bif lowerSelected q then
      (IntegralMixedVirtualContextLowerDispatcherBits.machine P a F h ha).model q else
      (IntegralMixedVirtualContextUpperDispatcherBits.machine P a F h).model q := by
  rw [Bool.cond_eq_ite]
  rfl

theorem model_phase (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (p : Phase) (q : List Bool) (hp25 : p.code ≤ 25)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : IntegralMixedVirtualContextBits.context P q) (hp : isPhase p q) :
    (machine P a F h ha).model q = IntegralMixedVirtualContextComponentBits.component P F p q := by
  rw [machine_model]
  by_cases hl : p.code ≤ 16
  · have HS : lowerSelected q = true := by
      unfold lowerSelected
      rw [hp]
      exact decide_eq_true hl
    rw [HS, Bool.cond_true, IntegralMixedVirtualContextComponentBits.component_lower P F p q hl]
    exact IntegralMixedVirtualContextLowerDispatcherBits.model_phase P a F h ha p q hl
      (by simp only [IntegralMixedVirtualContextBits.selected, hv, hr, hp, hx, and_self, decide_true])
  · have HS : lowerSelected q = false := by
      unfold lowerSelected
      rw [hp]
      exact decide_eq_false hl
    rw [HS, Bool.cond_false, IntegralMixedVirtualContextComponentBits.component_upper P F p q (by omega)]
    exact IntegralMixedVirtualContextUpperDispatcherBits.model_phase P a F h p q (by omega) hp25 hv hr hx hp

theorem model_invalid (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hv : ¬ IntegralMixedVirtualCaps.valid P q) :
    (machine P a F h ha).model q = [] := by
  rw [machine_model, IntegralMixedVirtualContextLowerDispatcherBits.model_invalid P a F h ha q hv,
    IntegralMixedVirtualContextUpperDispatcherBits.model_invalid P a F h q hv]
  cases lowerSelected q <;> rfl

theorem model_other_context (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (ha : SpaceFunction (originalScalar P F)) (q : List Bool) (hx : ¬ IntegralMixedVirtualContextBits.context P q) :
    (machine P a F h ha).model q = [] := by
  rw [machine_model, IntegralMixedVirtualContextLowerDispatcherBits.model_other_context P a F h ha q hx,
    IntegralMixedVirtualContextUpperDispatcherBits.model_other_context P a F h q hx]
  cases lowerSelected q <;> rfl
end LeanCanny.Algebra.IntegralMixedVirtualContextDispatcherBits

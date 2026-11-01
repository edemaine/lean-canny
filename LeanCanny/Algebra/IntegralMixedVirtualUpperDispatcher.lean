/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualUpperCanonical
/-! # One native dispatcher for virtual upper arithmetic phases seventeen to twenty-five

The creating-companion routine is separate. Other phases and invalid or
noncritical records return zero in this arithmetic dispatcher.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualUpperBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

structure Replies (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop where
  lower : LowerMatches P F answer
  leading : LeadingMatches P F answer
  reduction : ReductionMatches P F answer
  power : PowerMatches P F answer
  action : ActionMatches P F answer
  momentEntry : MomentMatches P F answer
  momentPower : MomentPowerMatches P F answer
  factor : FactorMatches P F answer
  relativePower : RelativePowerMatches P F answer

noncomputable def machine (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) : Machine :=
  (stage17 P a F h).choose ((stage18 P a F h).choose ((stage19 P a F h).choose
    ((stage21 P a F h).choose ((stage22 P a F h).choose ((stage23 P a F h).choose
      ((stage24 P a F h).choose ((stage25 P a F h).choose zero)))))))

private theorem right_selected (M N : Machine) (q : List Bool) (h : N.selected q = true) :
    (M.choose N).selected q = true := by
  change (M.selected q || N.selected q) = true
  rw [h, Bool.or_true]

theorem machine_selected (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (q : List Bool) : (machine P a F h).selected q = true := by
  unfold machine
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  apply right_selected
  rfl

theorem correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : Replies P F (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold machine
  apply choose_correct _ _ _ _ (correct17 P a F h g x hx.lower hx.leading)
  apply choose_correct _ _ _ _ (correct18 P a F h g _ hx.reduction)
  apply choose_correct _ _ _ _ (correct19 P a F h x hx.power)
  apply choose_correct _ _ _ _ (correct21_of_matches P a F h g x hx.action)
  apply choose_correct _ _ _ _ (correct22_of_matches P a F h g _ hx.momentEntry)
  apply choose_correct _ _ _ _ (correct23 P a F h g x hx.action hx.momentPower)
  apply choose_correct _ _ _ _ (correct24 P a F h g _ hx.factor)
  apply choose_correct _ _ _ _ (correct25_of_matches P a F h _ hx.relativePower hx.leading)
  exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedVirtualUpperDispatcherBits

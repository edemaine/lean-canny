/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualContextRelativeFactor
public import LeanCanny.Algebra.IntegralMixedVirtualContextCoefficient
public import LeanCanny.Algebra.IntegralMixedVirtualContextMomentPower
public import LeanCanny.Algebra.IntegralMixedVirtualUpperCanonical
/-! # One native dispatcher for virtual upper arithmetic phases seventeen to twenty-five

The creating-companion routine is separate. Other phases and invalid or
noncritical records return zero in this arithmetic dispatcher.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualContextUpperDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualContextUpperBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

structure Replies (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (answer : List Bool → List Bool) : Prop where
  entry : ∀ q, selectedFinite P .reductionEntry (reductionSize P F) q = true → EntryRepliesAt P F answer q
  reduction : ∀ q, selected P .reductionPower q = true → ReductionRepliesAt P F answer q
  power : ∀ q, selectedFinite P .actionEntry (reductionSize P F) q = true → ActionRepliesAt P F answer q
  action : ∀ q, selected P .momentEntry q = true → MomentEntryRepliesAt P a F h answer q
  momentEntry : ∀ q, selected P .momentPower q = true → IntegralCriticalFlatMomentBits.RepliesAt P (IntegralMixedVirtualUpperBits.characteristic P F) answer q
  relative : ∀ q, selectedFinite P .relativeFactor (factorSize P F) q = true → RelativeFactorRepliesAt P F answer q
  factor : ∀ q, selected P .relativePower q = true → FactorRepliesAt P F answer q
  coefficient : ∀ q, selected P .criticalCoefficient q = true → CoefficientRepliesAt P F answer q

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
    (x : (q : List Bool) → ZMod (modulus P q)) (hx : Replies P a F h (fun q => residueBits (x q))) :
    Correct (machine P a F h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  unfold machine
  apply choose_correct _ _ _ _ (correct17 P a F h g x hx.entry)
  apply choose_correct _ _ _ _ (correct18 P a F h g _ hx.reduction)
  apply choose_correct _ _ _ _ (correct19 P a F h x hx.power)
  apply choose_correct _ _ _ _ (correct21 P a F h g x hx.action)
  apply choose_correct _ _ _ _ (correct22 P a F h _ hx.momentEntry)
  apply choose_correct _ _ _ _ (correct23 P a F h g x hx.relative)
  apply choose_correct _ _ _ _ (correct24 P a F h _ hx.factor)
  apply choose_correct _ _ _ _ (correct25 P a F h _ hx.coefficient)
  exact zero_correct _ _

end LeanCanny.Algebra.IntegralMixedVirtualContextUpperDispatcherBits

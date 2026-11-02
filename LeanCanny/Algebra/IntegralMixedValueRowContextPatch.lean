/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueRowRequestContexts
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
/-! # Mathematical value-row replies outside virtual creating contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueRowScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualCaps
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 2 → 21 ≤ phase q → phase q ≤ 26 →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralMixedValueRowModel.component P F (phase q) q

structure External (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop where
  frozen : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 12 →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralMixedVirtualSnapshotBits.frozenLower P F q
  gradient : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 8 →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralMixedVirtualSpatialBits.cleared P F q
  critical : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 1 → phase q = 25 →
    IntegralMixedVirtualContextBits.context P q → answer q = (IntegralMixedVirtualTaskBits.source P F).value q
  originalScale : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 → phase q = 5 →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralMixedOriginalScaleBits.value P F q
  commonLeading : ∀ q, valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 → phase q = 3 →
    IntegralMixedVirtualContextBits.context P q → answer q = IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q

noncomputable def patch (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : List Bool :=
  if IntegralMixedVirtualContextBits.context P q then answer q else
  if IntegralMixedRoutineTaskBits.routine P q = 2 then IntegralMixedValueRowModel.value P F q else
  if IntegralMixedRoutineTaskBits.routine P q = 1 then
    if phase q = 12 then IntegralMixedVirtualSnapshotBits.frozenLower P F q else
    if phase q = 8 then IntegralMixedVirtualSpatialBits.cleared P F q else
    if phase q = 25 then (IntegralMixedVirtualTaskBits.source P F).value q else answer q
  else if IntegralMixedRoutineTaskBits.routine P q = 0 then
    if phase q = 5 then IntegralMixedOriginalScaleBits.value P F q else
    if phase q = 3 then IntegralCriticalLeadingBits.value (IntegralMixedVirtualTaskBits.arithmetic P F).toGradient.toFrozen q else answer q
  else answer q

theorem patch_good (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (hc : IntegralMixedVirtualContextBits.context P q) : patch P F answer q = answer q := by
  simp only [patch, ite_eq_left hc]

theorem patch_matches (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : Matches P F answer) :
    IntegralMixedValueRowModel.Matches P F (patch P F answer) := by
  intro q hv hr hlo hhi
  by_cases hc : IntegralMixedVirtualContextBits.context P q
  · rw [patch_good P F answer q hc]
    exact hm q hv hr hlo hhi hc
  · simp only [patch, ite_eq_right hc, ite_eq_left hr]
    exact IntegralMixedValueRowModel.value_matches P F q hv hr hlo hhi

theorem patch_external (P : Parameters) (F : Family) (answer : List Bool → List Bool) (hm : External P F answer) :
    IntegralMixedValueRowBoundaryReplies.External P F (patch P F answer) := by
  constructor
  · intro q hv hr hp
    by_cases hc : IntegralMixedVirtualContextBits.context P q
    · rw [patch_good P F answer q hc]; exact hm.frozen q hv hr hp hc
    · simp [patch, hc, hr, hp]
  · intro q hv hr hp
    by_cases hc : IntegralMixedVirtualContextBits.context P q
    · rw [patch_good P F answer q hc]; exact hm.gradient q hv hr hp hc
    · simp [patch, hc, hr, hp]
  · intro q hv hr hp
    by_cases hc : IntegralMixedVirtualContextBits.context P q
    · rw [patch_good P F answer q hc]; exact hm.critical q hv hr hp hc
    · simp [patch, hc, hr, hp]
  · intro q hv hr hp
    by_cases hc : IntegralMixedVirtualContextBits.context P q
    · rw [patch_good P F answer q hc]; exact hm.originalScale q hv hr hp hc
    · simp [patch, hc, hr, hp]
  · intro q hv hr hp
    by_cases hc : IntegralMixedVirtualContextBits.context P q
    · rw [patch_good P F answer q hc]; exact hm.commonLeading q hv hr hp hc
    · simp [patch, hc, hr, hp]
end LeanCanny.Algebra.IntegralMixedValueRowScopedBits

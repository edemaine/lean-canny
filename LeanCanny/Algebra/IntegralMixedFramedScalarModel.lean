/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalCurrent
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarMatches
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarMatches
public import LeanCanny.Algebra.IntegralMixedFramedScalarCells
/-! # Current scalar models for changing-source critical callbacks

These are pointwise semantic contracts for actual current task replies.
There is no scalar, height, bank or matrix SpaceFunction premise. Phase2's
retained-generator kernel is separate from the five current-source phases.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedScalarModelBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedScalarCellsBits (physicalFamily virtualFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def allowed (p : Phase) := IntegralMixedPhysicalScalarReplyBits.allowed p ∨ p = .productEntry

noncomputable def component (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (p : Phase) (q : List Bool) : List Bool :=
  if p = .productEntry then
    if get P .slot15 q = 1 then IntegralMixedPhysicalNativeScalarBits.value P (physicalFamily P D H) .originalScale q
    else IntegralMixedVirtualContextScalarBits.value P (virtualFamily P D H) .originalScale q
  else if get P .slot15 q = 1 then IntegralMixedPhysicalScalarReplyBits.component P (physicalFamily P D H) p q
  else IntegralMixedVirtualContextScalarReplyBits.component P (virtualFamily P D H) p q

abbrev Matches (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ p q, allowed p → IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 0 →
    (1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) → isPhase p q → answer q = component P D H p q

theorem component_physical (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (p : Phase) (q : List Bool) (hp : IntegralMixedPhysicalScalarReplyBits.allowed p) (hx : get P .slot15 q = 1) :
    component P D H p q = IntegralMixedPhysicalScalarReplyBits.component P (physicalFamily P D H) p q := by
  have HN : p ≠ .productEntry := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  rw [component, ite_eq_right HN, ite_eq_left hx]

theorem component_virtual (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (p : Phase) (q : List Bool) (hp : IntegralMixedVirtualContextScalarReplyBits.allowed p) (hx : IntegralMixedVirtualContextBits.context P q) :
    component P D H p q = IntegralMixedVirtualContextScalarReplyBits.component P (virtualFamily P D H) p q := by
  have HN : p ≠ .productEntry := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  have HX : get P .slot15 q ≠ 1 := by unfold IntegralMixedVirtualContextBits.context at hx; omega
  rw [component, ite_eq_right HN, ite_eq_right HX]

theorem physical_matches (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hm : Matches P D H answer) :
    IntegralMixedPhysicalScalarReplyBits.Matches P (physicalFamily P D H) answer := by
  intro p q hp hv hr hx hq
  exact (hm p q (Or.inl hp) hv hr (by omega) hq).trans (component_physical P D H p q hp hx)

theorem virtual_matches (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (answer : List Bool → List Bool) (hm : Matches P D H answer) :
    IntegralMixedVirtualContextScalarReplyBits.Matches P (virtualFamily P D H) answer := by
  intro p q hp hv hr hx hq
  have HA : IntegralMixedPhysicalScalarReplyBits.allowed p := hp
  have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by unfold IntegralMixedVirtualContextBits.context at hx; omega
  exact (hm p q (Or.inl HA) hv hr HX hq).trans (component_virtual P D H p q hp hx)

theorem component_canonical (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (p : Phase) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = component P D H p q := by
  unfold component
  split_ifs
  · exact IntegralMixedPhysicalNativeScalarBits.value_canonical P (physicalFamily P D H) .originalScale q
  · exact IntegralMixedVirtualContextScalarBits.value_canonical P (virtualFamily P D H) .originalScale q
  · exact IntegralMixedPhysicalScalarReplyBits.component_canonical P (physicalFamily P D H) p q
  · exact IntegralMixedVirtualContextScalarReplyBits.component_canonical P (virtualFamily P D H) p q

theorem critical_correct (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : IntegralMixedFramedCriticalBits.Controls P D H) (x : (q : List Bool) → ZMod (modulus P q))
    (hc : IntegralMixedFramedCriticalBits.Matches P a D H h (fun q => residueBits (x q)))
    (hs : Matches P D H (fun q => residueBits (x q))) :
    NativeControllerBranch.Correct (IntegralMixedFramedCriticalBits.machine P a D H h)
      (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedFramedCriticalBits.correct P a D H h x hc
    (physical_matches P D H _ hs) (virtual_matches P D H _ hs)
end LeanCanny.Algebra.IntegralMixedFramedScalarModelBits

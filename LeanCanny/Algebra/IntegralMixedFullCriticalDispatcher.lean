/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
public import LeanCanny.Algebra.IntegralMixedFullHistoryPhysicalBridge
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyMatching
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyMatching
/-! # Physical and virtual critical arithmetic share one native mixed dispatcher -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev physicalFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) :=
  IntegralMixedFullPhysicalBits.family P (IntegralMixedFullHistoryFamilyBits.physicalData P D)

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  full : IntegralMixedFullHistoryFamilyBits.Metadata P D
  physical : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D)
  physicalOriginal : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (physicalFamily P D))
  virtualOriginal : SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (IntegralMixedFullHistoryFamilyBits.family P D))

noncomputable def physicalMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedPhysicalDispatcherBits.machine P a (physicalFamily P D) h.physical h.physicalOriginal
noncomputable def virtualMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedVirtualContextDispatcherBits.machine P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.virtualOriginal

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : Machine :=
  (IntegralMixedRoutineContextGuard.machine P a 1 1 1 (physicalMachine P a D h)).choose
    ((IntegralMixedRoutineContextGuard.machine P a 1 2 4 (virtualMachine P a D h)).choose zero)

theorem physical_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (physicalMachine P a D h).selected q = true := by
  change (IntegralMixedPhysicalDispatcherBits.lowerSelected q ||
    (IntegralMixedPhysicalUpperDispatcherBits.machine P a (physicalFamily P D) h.physical).selected q) = true
  rw [IntegralMixedPhysicalUpperDispatcherBits.machine_selected, Bool.or_true]

theorem virtual_selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (virtualMachine P a D h).selected q = true := by
  change (IntegralMixedVirtualContextDispatcherBits.lowerSelected q ||
    (IntegralMixedVirtualContextUpperDispatcherBits.machine P a (IntegralMixedFullHistoryFamilyBits.family P D)
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full)).selected q) = true
  rw [IntegralMixedVirtualContextUpperDispatcherBits.machine_selected, Bool.or_true]

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) ||
    (decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) || true)) = true
  rw [Bool.or_true, Bool.or_true]

attribute [local irreducible] physicalMachine virtualMachine

theorem model_physical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hx : get P .slot15 q = 1) :
    (machine P a D h).model q = (physicalMachine P a D h).model q := by
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then _ else _) = _
  rw [ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_virtual (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hl : 2 ≤ get P .slot15 q) (hu : get P .slot15 q ≤ 4) :
    (machine P a D h).model q = (virtualMachine P a D h).model q := by
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then _ else
    if decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) then _ else _) = _
  have hn : ¬IntegralMixedRoutineContextGuard.Selected P 1 1 1 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn), ite_eq_left (by exact decide_eq_true ⟨hv, hr, hl, hu⟩)]
  rfl

end LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits

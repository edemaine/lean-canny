/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalFamily
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
public import LeanCanny.Algebra.IntegralMixedPhysicalScalarReplyMatching
public import LeanCanny.Algebra.IntegralMixedVirtualContextScalarReplyMatching
/-! # Native critical arithmetic over actual source-framed histories

Both existing critical kernels use the literal changing-source family. Numeric
controls come from represented command headers. Only the original physical and
virtual scalar coefficient readers are charged leaves; no interpreted-prefix
matrix reader is supplied. Original source-body writers remain separate.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable abbrev physicalFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedPhysicalBits.family P D H
noncomputable abbrev virtualFamily (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) :=
  IntegralMixedFramedHistoryFamilyBits.family P D H

structure Controls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  tables : IntegralMixedHeaderTablesBits.Tables
  native : IntegralMixedHeaderTablesBits.Access tables
  represents : IntegralMixedFramedHeaderBits.Represents P D H tables
  physicalOriginal : SpaceFunction (IntegralMixedPhysicalNativeLowerBits.originalScalar P (physicalFamily P D H))
  virtualOriginal : SpaceFunction (IntegralMixedVirtualNativeLowerBits.originalScalar P (virtualFamily P D H))

theorem physicalInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :
    IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D H) :=
  IntegralMixedFramedPhysicalBits.inputMetadata P a D H h.tables h.native h.represents

theorem virtualInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :
    IntegralMixedVirtualQueryBits.InputMetadata (virtualFamily P D H) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H h.tables h.native h.represents

noncomputable def physicalMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedPhysicalDispatcherBits.machine P a (physicalFamily P D H) (physicalInput P a D H h) h.physicalOriginal
noncomputable def virtualMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedVirtualContextDispatcherBits.machine P a (virtualFamily P D H)
    (virtualInput P a D H h) h.virtualOriginal

noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) : Machine :=
  (IntegralMixedRoutineContextGuard.machine P a 1 1 1 (physicalMachine P a D H h)).choose
    ((IntegralMixedRoutineContextGuard.machine P a 1 2 4 (virtualMachine P a D H h)).choose zero)

theorem physical_selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (physicalMachine P a D H h).selected q = true := by
  change (IntegralMixedPhysicalDispatcherBits.lowerSelected q ||
    (IntegralMixedPhysicalUpperDispatcherBits.machine P a (physicalFamily P D H) (physicalInput P a D H h)).selected q) = true
  rw [IntegralMixedPhysicalUpperDispatcherBits.machine_selected, Bool.or_true]

theorem virtual_selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (virtualMachine P a D H h).selected q = true := by
  change (IntegralMixedVirtualContextDispatcherBits.lowerSelected q ||
    (IntegralMixedVirtualContextUpperDispatcherBits.machine P a (virtualFamily P D H)
      (virtualInput P a D H h)).selected q) = true
  rw [IntegralMixedVirtualContextUpperDispatcherBits.machine_selected, Bool.or_true]

theorem selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (machine P a D H h).selected q = true := by
  change (decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) ||
    (decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) || true)) = true
  rw [Bool.or_true, Bool.or_true]

attribute [local irreducible] physicalMachine virtualMachine

theorem model_physical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hx : get P .slot15 q = 1) :
    (machine P a D H h).model q = (physicalMachine P a D H h).model q := by
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then _ else _) = _
  rw [ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_virtual (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hl : 2 ≤ get P .slot15 q) (hu : get P .slot15 q ≤ 4) :
    (machine P a D H h).model q = (virtualMachine P a D H h).model q := by
  change (if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then _ else
    if decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) then _ else _) = _
  have hn : ¬IntegralMixedRoutineContextGuard.Selected P 1 1 1 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn), ite_eq_left (by exact decide_eq_true ⟨hv, hr, hl, hu⟩)]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedCriticalBits

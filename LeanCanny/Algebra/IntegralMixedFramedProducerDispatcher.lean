/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedIntegerSource
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
public import LeanCanny.Algebra.IntegralMixedPhysicalCompanionDispatcher
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionScopedDispatcher
/-! # Native producer phases over the actual source-framed prefix

The original integer leaves charge exact degree and coefficients in Space.
Physical and normalized-cut producers reuse their existing current-reply
kernels. All source/header metadata is bound to the actual creating framed
instruction; no interpreted companion or leading cost is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerBits
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
  integer : IntegralMixedIntegerFamilyBits.Original P (IntegralMixedFramedIntegerBits.polynomial P D)

theorem physicalInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D H) :=
  IntegralMixedFramedPhysicalBits.inputMetadata P a D H h.tables h.native h.represents

theorem virtualInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedVirtualQueryBits.InputMetadata (virtualFamily P D H) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H h.tables h.native h.represents

theorem degreeInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : BinaryFn (virtualFamily P D H).degree :=
  IntegralMixedFramedHeaderBits.degree_binary P a D H h.tables h.native h.represents

noncomputable def integerMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) := IntegralMixedIntegerFamilyBits.machine P a (virtualFamily P D H) (virtualInput P a D H h)
      (IntegralMixedFramedIntegerBits.polynomial P D) h.integer
noncomputable def physicalMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) := IntegralMixedPhysicalCompanionDispatcherBits.machine P a (physicalFamily P D H) (physicalInput P a D H h)
noncomputable def cutMachine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) := IntegralMixedNormalizedCompanionDispatcherBits.machine P a (virtualFamily P D H)
      (virtualInput P a D H h) (degreeInput P a D H h)

abbrev InContext (P : Parameters) (lo hi : ℕ) := IntegralMixedRoutineContextGuard.Selected P 6 lo hi
noncomputable abbrev guarded (P : Parameters) (a : Access P) (lo hi : ℕ) (M : Machine) :=
  IntegralMixedRoutineContextGuard.machine P a 6 lo hi M

noncomputable def machine (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) : Machine :=
  (guarded P a 0 0 (integerMachine P a D H h)).choose
    ((guarded P a 1 1 (physicalMachine P a D H h)).choose
      ((guarded P a 2 4 (cutMachine P a D H h)).choose zero))

theorem selected (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (machine P a D H h).selected q = true := by
  change (decide (InContext P 0 0 q) || (decide (InContext P 1 1 q) || (decide (InContext P 2 4 q) || true))) = true
  rw [Bool.or_true, Bool.or_true, Bool.or_true]

attribute [local irreducible] integerMachine physicalMachine cutMachine

theorem model_integer (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hx : get P .slot15 q = 0) :
    (machine P a D H h).model q = (integerMachine P a D H h).model q := by
  change (if decide (InContext P 0 0 q) then _ else _) = _
  rw [ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_physical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hx : get P .slot15 q = 1) :
    (machine P a D H h).model q = (physicalMachine P a D H h).model q := by
  change (if decide (InContext P 0 0 q) then _ else if decide (InContext P 1 1 q) then _ else _) = _
  have hn : ¬InContext P 0 0 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn), ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_cut (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hl : 2 ≤ get P .slot15 q) (hu : get P .slot15 q ≤ 4) :
    (machine P a D H h).model q = (cutMachine P a D H h).model q := by
  change (if decide (InContext P 0 0 q) then _ else if decide (InContext P 1 1 q) then _ else if decide (InContext P 2 4 q) then _ else _) = _
  have hn0 : ¬InContext P 0 0 q := by intro hc; have := hc.2.2.2; omega
  have hn1 : ¬InContext P 1 1 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn0),
    ite_eq_right (by simpa only [decide_eq_true_eq] using hn1), ite_eq_left (by exact decide_eq_true ⟨hv, hr, hl, hu⟩)]
  rfl

end LeanCanny.Algebra.IntegralMixedFramedProducerBits

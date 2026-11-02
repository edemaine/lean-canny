/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedIntegerProducerSpaceDispatcher
public import LeanCanny.Algebra.IntegralMixedOldHeightCurrentProducers
public import LeanCanny.Algebra.IntegralMixedProducerCanonical
public import LeanCanny.Computation.NativeSingleCallBranch
/-! # One native dispatcher for the three actual mixed producer kinds -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  full : IntegralMixedFullHistoryFamilyBits.Metadata P D
  integer : IntegralMixedIntegerProducerSpaceBits.Original P D
  physical : IntegralMixedPhysicalQueryBits.InputMetadata (IntegralMixedPhysicalCompanionBits.fullFamily P D)

noncomputable def integerMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedIntegerProducerSpaceDispatcherBits.machine P a D h.integer
noncomputable def physicalMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedPhysicalCompanionDispatcherBits.machine P a (IntegralMixedPhysicalCompanionBits.fullFamily P D) h.physical
noncomputable def cutMachine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedNormalizedCompanionDispatcherBits.machine P a (IntegralMixedFullHistoryFamilyBits.family P D)
    (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree

def InContext (P : Parameters) (lo hi : ℕ) (q : List Bool) : Prop :=
  IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 6 ∧
    lo ≤ get P .slot15 q ∧ get P .slot15 q ≤ hi

theorem context_FP (P : Parameters) (a : Access P) (lo hi : ℕ) : FPPred (InContext P lo hi) :=
  (IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 6)).and
      (((BinaryFn.const lo).le (get_binary P a .slot15)).and ((get_binary P a .slot15).le (BinaryFn.const hi))))

noncomputable def guarded (P : Parameters) (a : Access P) (lo hi : ℕ) (M : Machine) : Machine :=
  M.withGuard (fun q => decide (InContext P lo hi q)) (context_FP P a lo hi).flag_mem_FP

noncomputable def machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) : Machine :=
  (guarded P a 0 0 (integerMachine P a D h)).choose
    ((guarded P a 1 1 (physicalMachine P a D h)).choose
      ((guarded P a 2 4 (cutMachine P a D h)).choose zero))

theorem selected (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool) :
    (machine P a D h).selected q = true := by
  change (decide (InContext P 0 0 q) || (decide (InContext P 1 1 q) || (decide (InContext P 2 4 q) || true))) = true
  rw [Bool.or_true, Bool.or_true, Bool.or_true]

attribute [local irreducible] integerMachine physicalMachine cutMachine

theorem model_integer (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hx : get P .slot15 q = 0) :
    (machine P a D h).model q = (integerMachine P a D h).model q := by
  change (if decide (InContext P 0 0 q) then _ else _) = _
  rw [ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_physical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6) (hx : get P .slot15 q = 1) :
    (machine P a D h).model q = (physicalMachine P a D h).model q := by
  change (if decide (InContext P 0 0 q) then _ else if decide (InContext P 1 1 q) then _ else _) = _
  have hn : ¬InContext P 0 0 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn), ite_eq_left (by exact decide_eq_true ⟨hv, hr, by omega, by omega⟩)]
  rfl

theorem model_cut (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 6)
    (hl : 2 ≤ get P .slot15 q) (hu : get P .slot15 q ≤ 4) :
    (machine P a D h).model q = (cutMachine P a D h).model q := by
  change (if decide (InContext P 0 0 q) then _ else if decide (InContext P 1 1 q) then _ else if decide (InContext P 2 4 q) then _ else _) = _
  have hn0 : ¬InContext P 0 0 q := by intro hc; have := hc.2.2.2; omega
  have hn1 : ¬InContext P 1 1 q := by intro hc; have := hc.2.2.2; omega
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hn0),
    ite_eq_right (by simpa only [decide_eq_true_eq] using hn1), ite_eq_left (by exact decide_eq_true ⟨hv, hr, hl, hu⟩)]
  rfl

end LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits

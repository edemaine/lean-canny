/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScalarLeading
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDenominator
public import LeanCanny.Algebra.IntegralMixedVirtualContextDenominator
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Concrete scalar machines over the actual full mixed history -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev physicalFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := IntegralMixedHeightCellsBits.physicalFamily P D
noncomputable abbrev virtualFamily (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := IntegralMixedOldHeightBits.bankFamily P D

structure Controls (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) where
  full : IntegralMixedFullHistoryFamilyBits.Metadata P D
  physical : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D)
  leading : IntegralMixedFullScalarLeadingBits.Primitive P D
  physicalScales : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (physicalFamily P D)
  virtualScales : IntegralMixedVirtualContextDenominatorBits.Primitive P (virtualFamily P D)
  height : IntegralMixedHeightCellsBits.Primitive P D

noncomputable def selected (P : Parameters) (p : Phase) (q : List Bool) : Bool :=
  decide (IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase p q ∧
    1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4)
theorem selected_iff (P : Parameters) (p : Phase) (q : List Bool) : selected P p q = true ↔
    IntegralMixedVirtualCaps.valid P q ∧ IntegralMixedRoutineTaskBits.routine P q = 0 ∧ isPhase p q ∧
      1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by simp only [selected, decide_eq_true_eq]
theorem selected_FP (P : Parameters) (a : Access P) (p : Phase) : (fun q => [selected P p q]) ∈ FP :=
  ((IntegralMixedVirtualCaps.valid_FP P a).and
    (((BinaryFn.ofUnary (IntegralMixedRoutineTaskBits.routine_unary P a)).eq (BinaryFn.const 0)).and
      ((isPhase_FP p).and (((BinaryFn.const 1).le (get_binary P a .slot15)).and ((get_binary P a .slot15).le (BinaryFn.const 4)))))).flag_mem_FP

noncomputable def physicalDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedPhysicalNativeDenominatorBits.machine P a (physicalFamily P D) h.physical
    (IntegralMixedFullPhysicalBits.geometry P (IntegralMixedFullHistoryFamilyBits.physicalData P D))
    (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.full) h.physicalScales
noncomputable def virtualDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedVirtualContextDenominatorBits.machine P a (virtualFamily P D) (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full)
    (IntegralMixedFullHistoryFamilyBits.geometry P D) (IntegralMixedFullHistoryFamilyBits.routing P D)
    (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.full) h.virtualScales
noncomputable def denominator (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (physicalDenominator P a D h).choose (virtualDenominator P a D h)

abbrev Kind := IntegralMixedPhysicalNativeScalarBits.Kind
def virtualKind : Kind → IntegralMixedVirtualContextScalarBits.Kind
  | .commonLeading => .commonLeading
  | .originalScale => .originalScale
noncomputable def physicalScalar (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (k : Kind) :=
  IntegralMixedPhysicalNativeScalarBits.machine P a (physicalFamily P D) h.physical k
noncomputable def virtualScalar (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (k : Kind) :=
  IntegralMixedVirtualContextScalarBits.machine P a (virtualFamily P D) (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) (virtualKind k)
noncomputable def scalar (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) (k : Kind) :=
  (physicalScalar P a D h k).choose (virtualScalar P a D h k)

noncomputable def oldHeight (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  (IntegralMixedFullOldHeightBits.machine P a D h.full).withGuard (selected P .clearedHeight) (selected_FP P a .clearedHeight)
noncomputable def height (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedNativeHeightBits.machine P a D (IntegralMixedFullHistoryFamilyBits.routing P D)
    (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.full) h.height
noncomputable def leading (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D) :=
  IntegralMixedFullScalarLeadingBits.machine P a D h.leading

end LeanCanny.Algebra.IntegralMixedFullScalarBits

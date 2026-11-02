/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarLeading
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDenominator
public import LeanCanny.Algebra.IntegralMixedVirtualContextDenominator
public import LeanCanny.Computation.NativePhaseDispatch
public import LeanCanny.Algebra.IntegralMixedFramedHeightCurrentReplies
/-! # Concrete scalar machines over the actual full mixed history -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFullScalarBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev physicalFamily (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) := IntegralMixedFramedScalarCellsBits.physicalFamily P D J
noncomputable abbrev virtualFamily (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) := IntegralMixedFramedOldHeightBits.bankFamily P D J

structure Controls (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  tables : IntegralMixedHeaderTablesBits.Tables
  native : IntegralMixedHeaderTablesBits.Access tables
  represents : IntegralMixedFramedHeaderBits.Represents P D J tables
  leading : IntegralMixedFramedScalarLeadingBits.Primitive P D J
  physicalScales : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (physicalFamily P D J)
  virtualScales : IntegralMixedVirtualContextDenominatorBits.Primitive P (virtualFamily P D J)
  height : IntegralMixedFramedScalarCellsBits.Primitive P D J

theorem physicalInput (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D J) :=
  IntegralMixedFramedPhysicalBits.inputMetadata P a D J h.tables h.native h.represents

theorem virtualInput (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedVirtualQueryBits.InputMetadata (virtualFamily P D J) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D J h.tables h.native h.represents

theorem routingAccess (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :
    IntegralMixedOldBankCofactorBits.RoutingAccess (IntegralMixedFramedHeaderBits.routing P D) :=
  IntegralMixedFramedHeaderBits.routingAccess P a D J h.tables h.native h.represents

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

noncomputable def physicalDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedPhysicalNativeDenominatorBits.machine P a (physicalFamily P D J) (physicalInput P a D J h)
    (IntegralMixedFramedPhysicalBits.geometry P D J)
    (IntegralMixedFramedHeaderBits.routing P D) (routingAccess P a D J h) h.physicalScales
noncomputable def virtualDenominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedVirtualContextDenominatorBits.machine P a (virtualFamily P D J) (virtualInput P a D J h)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D J) (IntegralMixedFramedHeaderBits.routing P D)
    (routingAccess P a D J h) h.virtualScales
noncomputable def denominator (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  (physicalDenominator P a D J h).choose (virtualDenominator P a D J h)

abbrev Kind := IntegralMixedPhysicalNativeScalarBits.Kind
def virtualKind : Kind → IntegralMixedVirtualContextScalarBits.Kind
  | .commonLeading => .commonLeading
  | .originalScale => .originalScale
noncomputable def physicalScalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  IntegralMixedPhysicalNativeScalarBits.machine P a (physicalFamily P D J) (physicalInput P a D J h) k
noncomputable def virtualScalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  IntegralMixedVirtualContextScalarBits.machine P a (virtualFamily P D J) (virtualInput P a D J h) (virtualKind k)
noncomputable def scalar (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) (k : Kind) :=
  (physicalScalar P a D J h k).choose (virtualScalar P a D J h k)

noncomputable def oldHeight (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  (IntegralMixedFramedOldHeightBits.machine P a D J h.tables h.native h.represents).withGuard (selected P .clearedHeight) (selected_FP P a .clearedHeight)
noncomputable def height (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedFramedNativeHeightBits.machine P a D J (IntegralMixedFramedHeaderBits.routing P D)
    (routingAccess P a D J h) h.height
noncomputable def leading (P : Parameters) (a : Access P) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D J) :=
  IntegralMixedFramedScalarLeadingBits.machine P a D J h.leading

end LeanCanny.Algebra.IntegralMixedFramedFullScalarBits

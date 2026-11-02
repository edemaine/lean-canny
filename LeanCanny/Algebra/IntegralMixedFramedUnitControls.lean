/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitCells
public import LeanCanny.Algebra.IntegralMixedFramedUnitScales
public import LeanCanny.Algebra.IntegralMixedFramedScalarLeading
/-! # Original-only controls for framed unit-selector scalar arithmetic

The encoded original body is selected at the saved birth. Literal syntax
agreement derives every cell cost; no interpreted denominator, retained height,
producer leading, or matrix evaluator is a control field.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitControlsBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedScalarCellsBits (physicalFamily virtualFamily)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) where
  tables : IntegralMixedHeaderTablesBits.Tables
  native : IntegralMixedHeaderTablesBits.Access tables
  represents : IntegralMixedFramedHeaderBits.Represents P D H tables
  writer : List Bool → List Bool
  writer_FP : writer ∈ FP
  snapshot : IntegralMixedFramedUnitSnapshotBits.Snapshot P D H writer

theorem physicalInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedPhysicalQueryBits.InputMetadata (physicalFamily P D H) :=
  IntegralMixedFramedPhysicalBits.inputMetadata P a D H h.tables h.native h.represents

theorem virtualInput (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedVirtualQueryBits.InputMetadata (virtualFamily P D H) :=
  IntegralMixedFramedPhysicalBits.virtualInputMetadata P a D H h.tables h.native h.represents

theorem routingAccess (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedOldBankCofactorBits.RoutingAccess (IntegralMixedFramedHeaderBits.routing P D) :=
  IntegralMixedFramedHeaderBits.routingAccess P a D H h.tables h.native h.represents

theorem leading (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedFramedScalarLeadingBits.Primitive P D H :=
  SpaceFunction.ofFP _ (IntegralMixedFramedUnitCellsBits.leading_FP P a D H h.writer h.snapshot)

theorem physicalScales (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedPhysicalNativeDenominatorBits.Primitive P (physicalFamily P D H) :=
  IntegralMixedFramedUnitScaleBits.physical_primitive P a D H h.writer h.snapshot

theorem virtualScales (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedVirtualContextDenominatorBits.Primitive P (virtualFamily P D H) :=
  IntegralMixedFramedUnitScaleBits.virtual_primitive P a D H h.writer h.snapshot

theorem cells (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) : IntegralMixedFramedScalarCellsBits.Primitive P D H :=
  IntegralMixedFramedUnitCellsBits.primitive P a D H h.writer h.writer_FP h.snapshot
end LeanCanny.Algebra.IntegralMixedFramedUnitControlsBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitSnapshot
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeDenominator
public import LeanCanny.Algebra.IntegralMixedVirtualContextDenominator
public import LeanCanny.Algebra.MatrixPowerArithmeticFP
/-! # Original unit scales need no bank or producer-leading evaluator -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedUnitScaleBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedScalarCellsBits (physicalFamily virtualFamily)
open IntegralMixedFramedUnitSnapshotBits (Snapshot)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical_scale (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) (i : ℕ) :
    IntegralMixedPhysicalDenominatorPostBits.scale P (physicalFamily P D H) q i = 1 := by
  unfold IntegralMixedPhysicalDenominatorPostBits.scale
  split_ifs
  · exact h.physicalScales _ _
  · rfl

theorem virtual_scale (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) (q : List Bool) (i : ℕ) :
    IntegralMixedVirtualDenominatorPostBits.scale P (virtualFamily P D H) q i = 1 := by
  unfold IntegralMixedVirtualDenominatorPostBits.scale
  split_ifs
  · exact h.virtualScales _ _
  · rfl

attribute [local irreducible] modulus

theorem physical_reader_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) :
    IntegralMixedPhysicalDenominatorPostBits.rawScaleReader P (physicalFamily P D H) ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  apply mem_FP_of_eq (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)
  intro z
  unfold IntegralMixedPhysicalDenominatorPostBits.rawScaleReader IntegralMixedPhysicalDenominatorPostBits.scaleAt
  rw [physical_scale P D H writer h]
  simpa only [Function.comp_apply, Int.cast_one] using ArithmeticBits.one_residueBits (modulus P (pairFst z))

theorem virtual_reader_FP (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) :
    IntegralMixedVirtualDenominatorPostBits.rawScaleReader P (virtualFamily P D H) ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  apply mem_FP_of_eq (mem_FP_comp HM.bits_mem_FP ArithmeticBits.one_mem_FP)
  intro z
  unfold IntegralMixedVirtualDenominatorPostBits.rawScaleReader IntegralMixedVirtualDenominatorPostBits.scaleAt
  rw [virtual_scale P D H writer h]
  simpa only [Function.comp_apply, Int.cast_one] using ArithmeticBits.one_residueBits (modulus P (pairFst z))

theorem physical_primitive (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) :
    IntegralMixedPhysicalNativeDenominatorBits.Primitive P (physicalFamily P D H) :=
  SpaceFunction.ofFP _ (physical_reader_FP P a D H writer h)

theorem virtual_primitive (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (writer : List Bool → List Bool) (h : Snapshot P D H writer) :
    IntegralMixedVirtualContextDenominatorBits.Primitive P (virtualFamily P D H) :=
  SpaceFunction.ofFP _ (virtual_reader_FP P a D H writer h)
end LeanCanny.Algebra.IntegralMixedFramedUnitScaleBits

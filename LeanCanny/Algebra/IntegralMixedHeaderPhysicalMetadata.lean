/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeaderMetadata
public import LeanCanny.Algebra.IntegralMixedFullHistoryPhysicalBridge
/-! # Physical critical metadata comes from the same original command headers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeaderTablesBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCommandHeaderBits
open scoped Classical

def physical (P : Parameters) (T : Tables) (key : List Bool) : Header :=
  if (producer P T key).context = 1 then producer P T key else zero

theorem physical_readers (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (T : Tables) (h : Access T) :
    Readers (physical P T) :=
  Readers.choose _ (((producer_readers P a T h).context).eq (BinaryFn.const 1)) (producer_readers P a T h)
    ⟨BinaryFn.const 0, BinaryFn.const 0, BinaryFn.const 0, BinaryFn.const 0, BinaryFn.const 0, BinaryFn.const 0, BinaryFn.const 0⟩

theorem physical_offset (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : Tables) (h : Represents P D T) (key : List Bool) :
    (physical P T key).offset =
      (IntegralMixedFullPhysicalBits.rule P (IntegralMixedFullHistoryFamilyBits.physicalData P D) key).offset.val := by
  unfold physical
  rw [producer_eq P D T h key]
  unfold IntegralMixedFullPhysicalBits.rule IntegralMixedFullHistoryFamilyBits.creatingCommand
  rw [IntegralMixedFullHistoryFamilyBits.physical_creating]
  cases hc : IntegralMixedFullHistoryFamilyBits.creating P D key with
  | none => rfl
  | some c => cases c with
    | integer => rfl
    | critical => rfl
    | cut r k => cases k <;> rfl

theorem physical_objective (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (T : Tables) (h : Represents P D T) (key : List Bool) :
    (physical P T key).objective =
      (IntegralMixedFullPhysicalBits.rule P (IntegralMixedFullHistoryFamilyBits.physicalData P D) key).objective := by
  unfold physical
  rw [producer_eq P D T h key]
  unfold IntegralMixedFullPhysicalBits.rule IntegralMixedFullHistoryFamilyBits.creatingCommand
  rw [IntegralMixedFullHistoryFamilyBits.physical_creating]
  cases hc : IntegralMixedFullHistoryFamilyBits.creating P D key with
  | none => rfl
  | some c => cases c with
    | integer => rfl
    | critical => rfl
    | cut r k => cases k <;> rfl

theorem physicalMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) (ht : Access T) (hr : Represents P D T) :
    IntegralMixedFullPhysicalBits.Metadata P (IntegralMixedFullHistoryFamilyBits.physicalData P D) where
  offset := by
    have H := UnaryFn.fromBitsLE_min (physical_readers P a T ht).offset.bits_mem_FP (a.ambient.comp pairFst_mem_FP)
    refine H.of_eq (fun key => ?_)
    rw [BinaryNatCode.encode, Nat.fromBitsLE_bits, physical_offset P D T hr key]
    exact min_eq_left (Nat.le_of_lt_succ (IntegralMixedFullPhysicalBits.rule P
      (IntegralMixedFullHistoryFamilyBits.physicalData P D) key).offset.isLt)
  objective := ((physical_readers P a T ht).objective).of_eq (physical_objective P D T hr)

theorem physicalInputMetadata (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (D : IntegralMixedFullHistoryFamilyBits.Data P) (T : Tables) (ht : Access T) (hr : Represents P D T) :
    IntegralMixedPhysicalQueryBits.InputMetadata
      (IntegralMixedFullPhysicalBits.family P (IntegralMixedFullHistoryFamilyBits.physicalData P D)) :=
  IntegralMixedFullPhysicalBits.inputMetadata P a (IntegralMixedFullHistoryFamilyBits.physicalData P D)
    (physicalMetadata P a D T ht hr)

end LeanCanny.Algebra.IntegralMixedHeaderTablesBits

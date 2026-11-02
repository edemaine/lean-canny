/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCanonicalUnitHeader
/-! # Native encoded headers from original unit record words -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderBits
open LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedUnitRecordCode (field physicalOffset virtualOffset)
open IntegralMixedCommandHeaderBits (Readers)
open scoped Classical

private theorem field_binary (w : List Bool → List Bool) (hw : w ∈ FP) (i : ℕ) :
    BinaryFn (fun q => Nat.fromBitsLE (field (w q) i)) :=
  BinaryFn.fromBits (mem_FP_comp (f:=w) (g:=fun v => WordList.get v i) hw (IntegralMixedCommandHeaderBits.get_FP i))

theorem virtualOffset_binary {n : List Bool → ℕ} (hn : UnaryFn n) (w : List Bool → List Bool) (hw : w ∈ FP) :
    BinaryFn (fun q => virtualOffset (n q) (w q)) := by
  exact ((field_binary w hw 2).mod (BinaryFn.ofUnary hn)).add (BinaryFn.const 1)

theorem physicalOffset_binary {n : List Bool → ℕ} (hn : UnaryFn n) (w : List Bool → List Bool) (hw : w ∈ FP) :
    BinaryFn (fun q => physicalOffset (n q) (w q)) := by
  exact (field_binary w hw 1).mod (BinaryFn.ofUnary (hn.add (UnaryFn.const 1)))

theorem virtualFree_unary {n : List Bool → ℕ} (hn : UnaryFn n) (w : List Bool → List Bool) (hw : w ∈ FP) :
    UnaryFn (fun q => virtualFree (n q) (w q)) := by
  have HB := ((BinaryFn.ofUnary hn).sub (virtualOffset_binary hn w hw)).add (BinaryFn.const 1)
  have HU := UnaryFn.fromBitsLE_min HB.bits_mem_FP (hn.add (UnaryFn.const 1))
  apply HU.of_eq
  intro q
  rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (Nat.add_le_add_right (Nat.sub_le (n q) (virtualOffset (n q) (w q))) 1)

theorem selection_readers {n degree : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn degree)
    (w : List Bool → List Bool) (hw : w ∈ FP) : Readers (fun q => selection (n q) (degree q) (w q)) := by
  have HO := virtualOffset_binary hn w hw
  have HF := BinaryFn.ofUnary (virtualFree_unary hn w hw)
  have HA := (IntegralMixedExceptionalBounds.auxiliaryCap_binary (hn.add (UnaryFn.const 1)) hD).add (BinaryFn.const 1)
  have HR := (PurePowerReductionBounds.dimension_binary (virtualFree_unary hn w hw) hD).add (BinaryFn.const 1)
  exact ⟨BinaryFn.const 2,(field_binary w hw 4).mod HF,HO,(field_binary w hw 3).mod HF,
    (field_binary w hw 9).mod HA,(field_binary w hw 8).mod HR,BinaryFn.const 5⟩

theorem physical_readers {n : List Bool → ℕ} (hn : UnaryFn n) (w : List Bool → List Bool) (hw : w ∈ FP) :
    Readers (fun q => physical (n q) (w q)) := by
  have HO := physicalOffset_binary hn w hw
  have HF := ((BinaryFn.ofUnary hn).sub HO).add (BinaryFn.const 1)
  exact ⟨BinaryFn.const 1,(field_binary w hw 4).mod HF,HO,(field_binary w hw 3).mod HF,
    BinaryFn.const 0,BinaryFn.const 0,BinaryFn.const 1⟩

theorem command_readers {n degree : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn degree)
    (w : List Bool → List Bool) (hw : w ∈ FP) : Readers (fun q => command (n q) (degree q) (w q)) := by
  have HP : FPPred (fun q => IntegralMixedUnitRecordCode.critical (w q)=true) :=
    FPPred.getBit (mem_FP_comp hw (IntegralMixedCommandHeaderBits.get_FP 0)) (UnaryFn.const 0)
  exact Readers.choose _ HP (physical_readers hn w hw) (selection_readers hn hD w hw)

theorem selection_FP {n degree : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn degree)
    (w : List Bool → List Bool) (hw : w ∈ FP) :
    (fun q => IntegralMixedCommandHeaderBits.encode (selection (n q) (degree q) (w q))) ∈ FP :=
  (selection_readers hn hD w hw).writer_FP

theorem command_FP {n degree : List Bool → ℕ} (hn : UnaryFn n) (hD : BinaryFn degree)
    (w : List Bool → List Bool) (hw : w ∈ FP) :
    (fun q => IntegralMixedCommandHeaderBits.encode (command (n q) (degree q) (w q))) ∈ FP :=
  (command_readers hn hD w hw).writer_FP

end LeanCanny.Algebra.IntegralMixedCanonicalUnitHeaderBits

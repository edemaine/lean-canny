/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedUnitRowCode
/-! # Native original unit-frame records

Fields: critical flag, physical offset, virtual offset, objective, coordinate,
physical frozen height, physical rows, virtual rows, choice, written degree.
The physical row vectors contain precisely n+1 entries. The auxiliary formal
nilpotent coordinate has no row in this encoding.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedUnitRecordCode
open LeanCanny.Algebra
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def field (code : List Bool) (i : ℕ) := WordList.get code i
def critical (code : List Bool) := (field code 0)[0]?.getD false
def physicalOffset (n : ℕ) (code : List Bool) := Nat.fromBitsLE (field code 1) % (n+1)
def virtualOffset (n : ℕ) (code : List Bool) := Nat.fromBitsLE (field code 2) % n + 1
def height (n : ℕ) (code : List Bool) := Nat.fromBitsLE (field code 5) % virtualOffset n code

noncomputable def physicalRows (n birth : ℕ) (code : List Bool) := if critical code then
  IntegralMixedUnitRowCode.table (pair (field code 6) (pair (BinaryNatCode.encode birth) (List.replicate (n+1) true))) else []
noncomputable def virtualRows (n birth : ℕ) (code : List Bool) :=
  IntegralMixedUnitRowCode.table (pair (field code 7) (pair (BinaryNatCode.encode birth) (List.replicate (n+1) true)))
noncomputable def body (n birth : ℕ) (code : List Bool) :=
  WordList.encode [BinaryNatCode.encode (height n code), physicalRows n birth code, virtualRows n birth code]

/-- Native packet consists of record, unary physical dimension, binary birth. -/
noncomputable def writer (p : List Bool) := body (pairFst (pairSnd p)).length (Nat.fromBitsLE (pairSnd (pairSnd p))) (pairFst p)

theorem field_FP (i : ℕ) : (fun p => field (pairFst p) i) ∈ FP :=
  mem_FP_comp (f := pairFst) (g := fun w => WordList.get w i) pairFst_mem_FP (IntegralMixedCommandHeaderBits.get_FP i)

theorem dimension_unary : UnaryFn (fun p : List Bool => (pairFst (pairSnd p)).length) :=
  UnaryFn.length (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

theorem height_binary : BinaryFn (fun p => height (pairFst (pairSnd p)).length (pairFst p)) :=
  (BinaryFn.fromBits (field_FP 5)).mod
    (((BinaryFn.fromBits (field_FP 2)).mod (BinaryFn.ofUnary dimension_unary)).add (BinaryFn.const 1))

def rowPacket (i : ℕ) (p : List Bool) := pair (field (pairFst p) i)
  (pair (pairSnd (pairSnd p)) (true :: pairFst (pairSnd p)))

theorem rowPacket_FP (i : ℕ) : rowPacket i ∈ FP :=
  mem_FP_pair (field_FP i) (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
    (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (cons_mem_FP true)))

theorem row_packet_eq (i : ℕ) (p : List Bool) : IntegralMixedUnitRowCode.table (rowPacket i p) =
    IntegralMixedUnitRowCode.table (pair (field (pairFst p) i)
      (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd (pairSnd p))))
        (List.replicate ((pairFst (pairSnd p)).length+1) true))) := by
  simp only [IntegralMixedUnitRowCode.table, rowPacket, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, List.length_cons, List.length_replicate]

attribute [local irreducible] body IntegralMixedUnitRowCode.table

theorem writer_FP : writer ∈ FP := by
  have HR (i : ℕ) := mem_FP_comp (rowPacket_FP i) IntegralMixedUnitRowCode.table_FP
  have HP := (FPPred.getBit (field_FP 0) (UnaryFn.const 0)).ite_mem_FP (HR 6) (constFn_mem_FP [])
  have HE := mem_FP_pair height_binary.bits_mem_FP (mem_FP_pair HP (mem_FP_pair (HR 7) (constFn_mem_FP [])))
  exact mem_FP_of_eq HE (fun p => by
    simp only [Function.comp_apply, writer, body, WordList.encode, physicalRows, virtualRows]
    rw [row_packet_eq, row_packet_eq]
    rfl)

theorem writer_packet (code : List Bool) (n birth : ℕ) :
    writer (pair code (pair (List.replicate n true) (BinaryNatCode.encode birth))) = body n birth code := by
  simp only [writer, pairFst_pair, pairSnd_pair, List.length_replicate, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem virtualOffset_le (n : ℕ) (hn : 0<n) (code : List Bool) : virtualOffset n code ≤ n := Nat.succ_le_of_lt (Nat.mod_lt _ hn)
theorem height_lt_offset (n : ℕ) (code : List Bool) : height n code < virtualOffset n code := Nat.mod_lt _ (Nat.succ_pos _)
theorem height_lt_arity (n : ℕ) (hn : 0<n) (code : List Bool) : height n code < n+1 :=
  (height_lt_offset n code).trans_le (Nat.le_succ_of_le (virtualOffset_le n hn code))
end LeanCanny.Encoding.IntegralMixedUnitRecordCode

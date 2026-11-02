/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedUnitBody
public import LeanCanny.Encoding.FrozenCoordinatePermutationFP
/-! # Literal causal unit-reference rows from original record words

Only original syntax is inspected. A reference is active precisely when its
flag is set and its index is strictly below the creating scalar birth. Row
vectors are truncated to physical source arity; no formal nilpotent row exists.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedUnitRowCode
open LeanCanny.Algebra IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def producer (code : List Bool) (i : ℕ) := Nat.fromBitsLE (pairSnd (WordList.get code i))
def reference (code : List Bool) (birth i : ℕ) := birth - 1 - producer code i
def active (code : List Bool) (birth i : ℕ) : Prop :=
  (pairFst (WordList.get code i))[0]?.getD false = true ∧ producer code i < birth

noncomputable def row (code : List Bool) (birth i : ℕ) := pair [decide (active code birth i)] (BinaryNatCode.encode (reference code birth i))
noncomputable def expression (code : List Bool) (birth i : ℕ) : AffineExpr :=
  if active code birth i then .reference (reference code birth i) else .constant 0

def payload (z : List Bool) := WordList.reader
  (pair (pairFst (pairFst z)) (BinaryNatCode.encode (pairSnd z).length))

theorem payload_FP : payload ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP) WordList.reader_FP

noncomputable def entry (z : List Bool) := row (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd (pairFst z))) (pairSnd z).length

theorem entry_FP : entry ∈ FP := by
  have HF := FPPred.getBit (mem_FP_comp payload_FP pairFst_mem_FP) (UnaryFn.const 0)
  have HR := BinaryFn.fromBits (mem_FP_comp payload_FP pairSnd_mem_FP)
  have HB := BinaryFn.fromBits (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)
  have HA : FPPred (fun z => active (pairFst (pairFst z)) (Nat.fromBitsLE (pairSnd (pairFst z))) (pairSnd z).length) :=
    (HF.and (HR.lt HB)).of_iff (fun z => by
      simp only [Function.comp_apply, payload, WordList.reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, producer, active])
  exact mem_FP_of_eq (mem_FP_pair HA.flag_mem_FP ((HB.sub (BinaryFn.const 1)).sub HR).bits_mem_FP)
    (fun z => by simp only [Function.comp_apply, payload, WordList.reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)

/-- Packet: original row table, binary creating birth, unary physical arity. -/
noncomputable def table (p : List Bool) := WordList.encode ((List.range (pairSnd (pairSnd p)).length).map
  (row (pairFst p) (Nat.fromBitsLE (pairFst (pairSnd p)))))

noncomputable def tableEntry (z : List Bool) := pair (entry (pair (pair (pairFst (pairFst z)) (pairFst (pairSnd (pairFst z)))) (pairSnd z))) []

attribute [local irreducible] entry row active reference producer

theorem table_FP : table ∈ FP := by
  have HC := mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)) pairSnd_mem_FP
  have HE : tableEntry ∈ FP := mem_FP_pair (mem_FP_comp HC entry_FP) (constFn_mem_FP [])
  apply mem_FP_of_eq (flatMap_range_mem_FP HE (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
  intro p
  simp only [table, FrozenCoordinatePermutationBits.encode_flatMap, List.flatMap_map,
    tableEntry, entry, pairFst_pair, pairSnd_pair, List.length_replicate, Function.comp_apply]

theorem table_packet (code : List Bool) (birth arity : ℕ) :
    table (pair code (pair (BinaryNatCode.encode birth) (List.replicate arity true))) =
      WordList.encode ((List.range arity).map (row code birth)) := by
  simp only [table, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, List.length_replicate]

theorem get_table (code : List Bool) (birth arity i : ℕ) (hi : i < arity) :
    WordList.get (WordList.encode ((List.range arity).map (row code birth))) i = row code birth i := by
  rw [WordList.get_encode]
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem get_table_outside (code : List Bool) (birth arity i : ℕ) (hi : arity ≤ i) :
    WordList.get (WordList.encode ((List.range arity).map (row code birth))) i = [] := by
  rw [WordList.get_encode, List.getElem?_eq_none (by simpa only [List.length_map, List.length_range] using hi)]
  rfl

theorem producer_bound (code : List Bool) (birth i : ℕ) (h : active code birth i) : producer code i < birth := by
  unfold active at h
  exact h.2

theorem active_bound (code : List Bool) (birth i : ℕ) (h : active code birth i) : reference code birth i < birth := by
  unfold active at h
  have H := h.2
  unfold reference
  omega

theorem empty_birth (code : List Bool) (i : ℕ) : expression code 0 i = .constant 0 := by
  unfold expression
  apply ite_eq_right
  intro h
  unfold active at h
  exact Nat.not_lt_zero _ h.2
end LeanCanny.Encoding.IntegralMixedUnitRowCode

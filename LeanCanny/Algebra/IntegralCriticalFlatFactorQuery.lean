/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatMonomialSource

/-! # Fresh flat monomial-factor requests

The position uses slot 8; old-basis row and column replace their matrix
fields. Original-grid index, expression, derivative, root and birth survive.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFactorQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks

def reader (P : IntegralCriticalHistoryTask.Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = 1 then IntegralPowerProductBits.rowWord (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 2 then IntegralPowerProductBits.colWord (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 8 then IntegralPowerProductBits.factorWord (pairFst z) else
    IntegralCriticalFlatMatrixQuery.saved P z

theorem reader_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : reader P ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  exact (HI.eq (BinaryFn.const 1)).ite_mem_FP
    (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.rowWord) pairFst_mem_FP IntegralPowerProductBits.rowWord_FP)
    ((HI.eq (BinaryFn.const 2)).ite_mem_FP
      (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.colWord) pairFst_mem_FP IntegralPowerProductBits.colWord_FP)
      ((HI.eq (BinaryFn.const 8)).ite_mem_FP
        (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.factorWord) pairFst_mem_FP IntegralPowerProductBits.factorWord_FP)
        (IntegralCriticalFlatEulerRowsBits.copyReader_FP P a)))

def writer (P : IntegralCriticalHistoryTask.Parameters) (p : IntegralCriticalHistoryTask.Phase) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child P pairFst (IntegralCriticalHistoryTask.birth P ∘ pairFst) p (reader P)

theorem writer_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (p : IntegralCriticalHistoryTask.Phase) : writer P p ∈ FP :=
  IntegralCriticalHistoryTask.child_FP P a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary P a))).comp pairFst_mem_FP)
    p _ (reader_FP P a)

theorem reader_packet (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (i : ℕ) :
    reader P (pair p (BinaryNatCode.encode i)) =
      if i = 1 then IntegralPowerProductBits.rowWord p else
      if i = 2 then IntegralPowerProductBits.colWord p else
      if i = 8 then IntegralPowerProductBits.factorWord p else BinaryNatCode.encode
        (RankedHistoryFields.get (IntegralCriticalHistoryTask.numericCap P) 16 (pairFst p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [reader, pairFst_pair, pairSnd_pair, HI]
  unfold IntegralCriticalFlatMatrixQuery.saved
  simp only [pairFst_pair, pairSnd_pair]
  rw [RankedHistoryFields.read_packet]

theorem writer_get (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) =
      if f = .row then min (Nat.fromBitsLE (IntegralPowerProductBits.rowWord p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p))) else
      if f = .col then min (Nat.fromBitsLE (IntegralPowerProductBits.colWord p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p))) else
      if f = .slot8 then min (Nat.fromBitsLE (IntegralPowerProductBits.factorWord p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p))) else
        IntegralCriticalHistoryTask.get P f (pairFst p) := by
  have H := IntegralCriticalHistoryTask.get_le P f (pairFst p)
  rw [writer, IntegralCriticalHistoryTask.child_get, reader_packet]
  cases f <;> norm_num only [IntegralCriticalHistoryTask.Field.code, reduceCtorEq, ite_true, ite_false,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem writer_other (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) (hr : f ≠ .row) (hc : f ≠ .col) (hs : f ≠ .slot8) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) = IntegralCriticalHistoryTask.get P f (pairFst p) := by
  rw [writer_get, ite_eq_right hr, ite_eq_right hc, ite_eq_right hs]

theorem writer_packet_fields (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (s r t : ℕ)
    (hs : s ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (hr : r ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c))
    (ht : t ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    let w := writer P phase (IntegralMonomialTermBits.packet c s r t)
    IntegralCriticalHistoryTask.get P .slot8 w = s ∧
      IntegralCriticalHistoryTask.get P .row w = r ∧ IntegralCriticalHistoryTask.get P .col w = t := by
  dsimp only
  simp only [writer_get, IntegralMonomialTermBits.packet, IntegralPowerProductBits.factorWord,
    IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord, pairFst_pair, pairSnd_pair,
    reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact ⟨min_eq_left hs, min_eq_left hr, min_eq_left ht⟩

theorem writer_root (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    RankedHistoryTask.root (writer P phase p) = RankedHistoryTask.root (pairFst p) :=
  IntegralCriticalHistoryTask.child_root P _ _ _ _ p

theorem writer_birth (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.birth P (writer P phase p) = IntegralCriticalHistoryTask.birth P (pairFst p) := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_phase (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.phase (writer P phase p) = phase.code := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ phase.code_lt

theorem writer_modulus (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus P (writer P phase p) = IntegralCriticalHistoryTask.modulus P (pairFst p) := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [writer_other P phase p .modulus (by decide) (by decide) (by decide)]

theorem writer_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool)
    (hp : phase.code < IntegralCriticalHistoryTask.phase (pairFst p)) :
    IntegralCriticalHistoryTask.rank P (writer P phase p) < IntegralCriticalHistoryTask.rank P (pairFst p) :=
  IntegralCriticalHistoryTask.child_lower_phase P pairFst _ phase _ p rfl hp

theorem writer_tasks (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (r p : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r (pairFst p)) : IntegralCriticalHistoryTask.Tasks P r (writer P phase p) :=
  IntegralCriticalHistoryTask.child_tasks P pairFst _ phase _ r p ht (min_le_right _ _)

theorem writer_length (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (p : List Bool) :
    (writer P phase p).length ≤ IntegralCriticalHistoryTask.wordBudget P (pairFst p) :=
  IntegralCriticalHistoryTask.child_length P pairFst _ phase _ p (min_le_right _ _)

def input (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .slot8 c))
    (pair (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .row c))
      (BinaryNatCode.encode (IntegralCriticalHistoryTask.get P .col c))))

theorem input_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : input P ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (IntegralCriticalHistoryTask.get_binary P a .slot8).bits_mem_FP
    (mem_FP_pair (IntegralCriticalHistoryTask.get_binary P a .row).bits_mem_FP
      (IntegralCriticalHistoryTask.get_binary P a .col).bits_mem_FP))

theorem input_parent (P : IntegralCriticalHistoryTask.Parameters) (c : List Bool) : pairFst (input P c) = c := by
  unfold input
  exact pairFst_pair _ _

end LeanCanny.Algebra.IntegralCriticalFlatFactorQuery

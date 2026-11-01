/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatGenericGrid
/-! # Fresh flat retained-coordinate requests -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatCoordinateQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
def reader (P : IntegralCriticalHistoryTask.Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = IntegralCriticalHistoryTask.Field.slot8.code then pairSnd (pairFst z)
  else IntegralCriticalFlatMatrixQuery.saved P z

theorem reader_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P) : reader P ∈ FP := by
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd z)) := BinaryFn.fromBits pairSnd_mem_FP
  have HK := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have HC := IntegralCriticalFlatEulerRowsBits.copyReader_FP P a
  exact (HI.eq (BinaryFn.const 8)).ite_mem_FP HK HC

def writer (P : IntegralCriticalHistoryTask.Parameters) (p : IntegralCriticalHistoryTask.Phase) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child P pairFst (IntegralCriticalHistoryTask.birth P ∘ pairFst) p (reader P)

theorem writer_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (p : IntegralCriticalHistoryTask.Phase) : writer P p ∈ FP :=
  IntegralCriticalHistoryTask.child_FP P a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary P a))).comp pairFst_mem_FP)
    p _ (reader_FP P a)

theorem reader_packet (P : IntegralCriticalHistoryTask.Parameters) (p : List Bool) (i : ℕ) :
    reader P (pair p (BinaryNatCode.encode i)) =
      if i = 8 then pairSnd p else BinaryNatCode.encode
        (RankedHistoryFields.get (IntegralCriticalHistoryTask.numericCap P) 16 (pairFst p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [reader, IntegralCriticalFlatMatrixQuery.saved, pairFst_pair, pairSnd_pair, HI,
    IntegralCriticalHistoryTask.Field.code]
  rw [RankedHistoryFields.read_packet]

theorem writer_get (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) =
      if f = .slot8 then min (Nat.fromBitsLE (pairSnd p))
        (IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root (pairFst p)))
      else IntegralCriticalHistoryTask.get P f (pairFst p) := by
  have H := IntegralCriticalHistoryTask.get_le P f (pairFst p)
  rw [writer, IntegralCriticalHistoryTask.child_get, reader_packet]
  cases f <;> norm_num only [IntegralCriticalHistoryTask.Field.code, reduceCtorEq, ite_true, ite_false,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem writer_coordinate (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (k : ℕ) (hk : k ≤ IntegralCriticalHistoryTask.numericCap P (RankedHistoryTask.root c)) :
    IntegralCriticalHistoryTask.get P .slot8 (writer P phase (pair c (BinaryNatCode.encode k))) = k := by
  rw [writer_get]
  simp only [ite_true, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact min_eq_left hk

theorem writer_other (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (p : List Bool) (f : IntegralCriticalHistoryTask.Field) (hf : f ≠ .slot8) :
    IntegralCriticalHistoryTask.get P f (writer P phase p) = IntegralCriticalHistoryTask.get P f (pairFst p) := by
  rw [writer_get, ite_eq_right hf]

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
  rw [writer_other P phase p .modulus (by decide)]

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


end LeanCanny.Algebra.IntegralCriticalFlatCoordinateQuery

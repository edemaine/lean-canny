/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalHistoryTask

/-! # Flat entry queries shared by the critical matrix-power stages

A streamed matrix-power request supplies `pair parent (pair row col)`.
The writer keeps the root and birth, replaces both matrix indices, and
copies the other bounded fields into a fresh task at its entry phase.
No suspended matrix-power context is retained by the child.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false

def saved (F : Parameters) (z : List Bool) : List Bool :=
  RankedHistoryFields.read (numericCap F) 16 (pair (pairFst (pairFst z)) (pairSnd z))

def reader (F : Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.row.code then pairFst (pairSnd (pairFst z)) else
    if Nat.fromBitsLE (pairSnd z) = Field.col.code then pairSnd (pairSnd (pairFst z)) else saved F z

theorem reader_FP (F : Parameters) (a : Access F) : reader F ∈ FP := by
  have HR := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP
  have HC := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
  have HS := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap F) 16 (numericCap_binary F a))
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.row.code)).ite_mem_FP HR
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.col.code)).ite_mem_FP HC HS)

def writer (F : Parameters) (entryPhase : Phase) : List Bool → List Bool :=
  child F pairFst (birth F ∘ pairFst) entryPhase (reader F)

theorem writer_FP (F : Parameters) (a : Access F) (entryPhase : Phase) : writer F entryPhase ∈ FP :=
  child_FP F a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary F a))).comp pairFst_mem_FP)
    entryPhase (reader F) (reader_FP F a)

theorem reader_packet (F : Parameters) (p : List Bool) (i : ℕ) :
    reader F (pair p (BinaryNatCode.encode i)) =
      if i = Field.row.code then pairFst (pairSnd p) else
        if i = Field.col.code then pairSnd (pairSnd p) else
          BinaryNatCode.encode (RankedHistoryFields.get (numericCap F) 16 (pairFst p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [reader, saved, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet (numericCap F) 16 (pairFst p) i]

theorem writer_root (F : Parameters) (entryPhase : Phase) (p : List Bool) :
    RankedHistoryTask.root (writer F entryPhase p) = RankedHistoryTask.root (pairFst p) :=
  child_root F pairFst _ entryPhase _ p

theorem writer_birth (F : Parameters) (entryPhase : Phase) (p : List Bool) :
    birth F (writer F entryPhase p) = birth F (pairFst p) := by
  unfold writer child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem child_phase (F : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ)
    (entryPhase : Phase) (reader : List Bool → List Bool) (p : List Bool) :
    phase (child F parent b entryPhase reader p) = entryPhase.code := by
  unfold child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ entryPhase.code_lt

theorem writer_phase (F : Parameters) (entryPhase : Phase) (p : List Bool) :
    phase (writer F entryPhase p) = entryPhase.code := by
  unfold writer child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ entryPhase.code_lt

theorem writer_get (F : Parameters) (entryPhase : Phase) (p : List Bool) (f : Field) :
    get F f (writer F entryPhase p) =
      if f = .row then min (Nat.fromBitsLE (pairFst (pairSnd p))) (numericCap F (RankedHistoryTask.root (pairFst p))) else
        if f = .col then min (Nat.fromBitsLE (pairSnd (pairSnd p))) (numericCap F (RankedHistoryTask.root (pairFst p))) else
          get F f (pairFst p) := by
  have H := RankedHistoryFields.get_le (numericCap F) 16 (pairFst p) f.code
  rw [writer, child_get, reader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem writer_modulus (F : Parameters) (entryPhase : Phase) (p : List Bool) :
    IntegralCriticalHistoryTask.modulus F (writer F entryPhase p) = IntegralCriticalHistoryTask.modulus F (pairFst p) := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [writer_get]
  rfl

theorem writer_lower_rank (F : Parameters) (entryPhase : Phase) (p : List Bool)
    (hp : entryPhase.code < phase (pairFst p)) : rank F (writer F entryPhase p) < rank F (pairFst p) :=
  child_lower_phase F pairFst _ entryPhase _ p rfl hp

theorem writer_tasks (F : Parameters) (entryPhase : Phase) (r p : List Bool)
    (h : Tasks F r (pairFst p)) : Tasks F r (writer F entryPhase p) :=
  child_tasks F pairFst _ entryPhase _ r p h (min_le_right _ _)

theorem writer_length (F : Parameters) (entryPhase : Phase) (p : List Bool) :
    (writer F entryPhase p).length ≤ wordBudget F (pairFst p) :=
  child_length F pairFst _ entryPhase _ p (min_le_right _ _)

end LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
/-! # Fresh lower-row coefficient requests for pure-power reduction

The original row/column basis ranks survive; the requested lower-row index
and spatial exponent become the derivative and target fields at phase16.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatLowerQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
def saved (F : Parameters) (z : List Bool) : List Bool :=
  RankedHistoryFields.read (numericCap F) 16 (pair (original (pairFst z)) (pairSnd z))

def reader (F : Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = 1 then basisRowCode (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 2 then basisColCode (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 6 then MatrixMoment.EntryBits.rowIndex (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 4 then MatrixMoment.EntryBits.colIndex (pairFst z) else saved F z

theorem reader_FP (F : Parameters) (a : IntegralCriticalHistoryTask.Access F) : reader F ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HS := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP original_FP) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap F) 16 (numericCap_binary F a))
  exact (HI.eq (BinaryFn.const 1)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := basisRowCode) pairFst_mem_FP basisRowCode_FP)
    ((HI.eq (BinaryFn.const 2)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := basisColCode) pairFst_mem_FP basisColCode_FP)
      ((HI.eq (BinaryFn.const 6)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := MatrixMoment.EntryBits.rowIndex) pairFst_mem_FP MatrixMoment.EntryBits.rowIndex_mem_FP)
        ((HI.eq (BinaryFn.const 4)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := MatrixMoment.EntryBits.colIndex) pairFst_mem_FP MatrixMoment.EntryBits.colIndex_mem_FP) HS)))

def writer (F : Parameters) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child F original (birth F ∘ original) .eulerLower (reader F)

theorem writer_FP (F : Parameters) (a : IntegralCriticalHistoryTask.Access F) : writer F ∈ FP :=
  child_FP F a original original_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary F a))).comp original_FP)
    .eulerLower _ (reader_FP F a)

theorem reader_packet (F : Parameters) (p : List Bool) (i : ℕ) :
    reader F (pair p (BinaryNatCode.encode i)) =
      if i = 1 then basisRowCode p else if i = 2 then basisColCode p else
      if i = 6 then MatrixMoment.EntryBits.rowIndex p else if i = 4 then MatrixMoment.EntryBits.colIndex p else
      BinaryNatCode.encode (RankedHistoryFields.get (numericCap F) 16 (original p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [reader, saved, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem writer_get (F : Parameters) (p : List Bool) (f : Field) :
    get F f (writer F p) =
      if f = .row then min (Nat.fromBitsLE (basisRowCode p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .col then min (Nat.fromBitsLE (basisColCode p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .derivative then min (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .target then min (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p)) (numericCap F (RankedHistoryTask.root (original p))) else
      get F f (original p) := by
  have H := get_le F f (original p)
  rw [writer, IntegralCriticalHistoryTask.child_get, reader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem writer_root (F : Parameters) (p : List Bool) :
    RankedHistoryTask.root (writer F p) = RankedHistoryTask.root (original p) :=
  child_root F _ _ _ _ p

theorem writer_birth (F : Parameters) (p : List Bool) : birth F (writer F p) = birth F (original p) := by
  unfold writer IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_phase (F : Parameters) (p : List Bool) : phase (writer F p) = 16 :=
  IntegralCriticalFlatMatrixQuery.child_phase F _ _ .eulerLower _ p

theorem writer_modulus (F : Parameters) (p : List Bool) : modulus F (writer F p) = modulus F (original p) := by
  unfold modulus
  rw [writer_get]
  rfl

theorem writer_lower_rank (F : Parameters) (p : List Bool)
    (hp : 16 < phase (original p)) : rank F (writer F p) < rank F (original p) :=
  child_lower_phase F original _ .eulerLower _ p rfl hp

theorem writer_tasks (F : Parameters) (r p : List Bool)
    (hp : Tasks F r (original p)) : Tasks F r (writer F p) :=
  child_tasks F original _ .eulerLower _ r p hp (min_le_right _ _)

theorem writer_length (F : Parameters) (p : List Bool) :
    (writer F p).length ≤ wordBudget F (original p) :=
  child_length F original _ .eulerLower _ p (min_le_right _ _)

end LeanCanny.Algebra.IntegralCriticalFlatLowerQuery

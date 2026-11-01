/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery
public import LeanCanny.Algebra.IntegralBerkowitzBlockController

/-! # Fresh relative-factor diagonal and moment tasks

Integer block indices combine the old-basis rank with the spatial index.
Moment tasks retain both spatial factor indices in slots eleven and twelve,
and the old-basis indices in the ordinary row and column fields.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false

def entryPacket (S : Source) (p : List Bool) : List Bool :=
  pair (original p) (pair
    (BinaryNatCode.encode (Nat.fromBitsLE (basisRowCode p) + S.rank (original p) * Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)))
    (BinaryNatCode.encode (Nat.fromBitsLE (basisColCode p) + S.rank (original p) * Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p))))

theorem entryPacket_FP (S : Source) (a : IntegralBerkowitzBlockBits.Access S) : entryPacket S ∈ FP := by
  have HR := (BinaryFn.fromBits basisRowCode_FP).add ((originalRank_binary S a).mul (BinaryFn.fromBits MatrixMoment.EntryBits.rowIndex_mem_FP))
  have HC := (BinaryFn.fromBits basisColCode_FP).add ((originalRank_binary S a).mul (BinaryFn.fromBits MatrixMoment.EntryBits.colIndex_mem_FP))
  exact mem_FP_pair original_FP (mem_FP_pair HR.bits_mem_FP HC.bits_mem_FP)

def entryWriter (F : Parameters) (S : Source) : List Bool → List Bool :=
  IntegralCriticalFlatMatrixQuery.writer F .actionEntry ∘ entryPacket S

theorem entryWriter_FP (F : Parameters) (h : IntegralCriticalHistoryTask.Access F)
    (S : Source) (a : IntegralBerkowitzBlockBits.Access S) : entryWriter F S ∈ FP :=
  mem_FP_comp (entryPacket_FP S a) (IntegralCriticalFlatMatrixQuery.writer_FP F h .actionEntry)

theorem entry_parent (S : Source) (p : List Bool) : pairFst (entryPacket S p) = original p := by
  simp only [entryPacket, pairFst_pair]

theorem entryWriter_root (F : Parameters) (S : Source) (p : List Bool) :
    RankedHistoryTask.root (entryWriter F S p) = RankedHistoryTask.root (original p) := by
  exact (IntegralCriticalFlatMatrixQuery.writer_root F .actionEntry _).trans (congrArg RankedHistoryTask.root (entry_parent S p))

theorem entryWriter_lower_rank (F : Parameters) (S : Source) (p : List Bool)
    (hp : 19 < phase (original p)) : rank F (entryWriter F S p) < rank F (original p) := by
  have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank F .actionEntry (entryPacket S p)
  rw [entry_parent] at H
  exact H hp

theorem entryWriter_tasks (F : Parameters) (S : Source) (r p : List Bool)
    (hp : Tasks F r (original p)) : Tasks F r (entryWriter F S p) := by
  apply IntegralCriticalFlatMatrixQuery.writer_tasks
  simpa only [entry_parent] using hp

def momentSaved (F : Parameters) (z : List Bool) : List Bool :=
  RankedHistoryFields.read (numericCap F) 16 (pair (original (pairFst z)) (pairSnd z))

def momentReader (F : Parameters) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = 1 then basisRowCode (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 2 then basisColCode (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 11 then MatrixMoment.EntryBits.rowIndex (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = 12 then MatrixMoment.EntryBits.colIndex (pairFst z) else momentSaved F z

theorem momentReader_FP (F : Parameters) (a : IntegralCriticalHistoryTask.Access F) : momentReader F ∈ FP := by
  have HI := BinaryFn.fromBits pairSnd_mem_FP
  have HS := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP original_FP) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap F) 16 (numericCap_binary F a))
  exact (HI.eq (BinaryFn.const 1)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := basisRowCode) pairFst_mem_FP basisRowCode_FP)
    ((HI.eq (BinaryFn.const 2)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := basisColCode) pairFst_mem_FP basisColCode_FP)
      ((HI.eq (BinaryFn.const 11)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := MatrixMoment.EntryBits.rowIndex) pairFst_mem_FP MatrixMoment.EntryBits.rowIndex_mem_FP)
        ((HI.eq (BinaryFn.const 12)).ite_mem_FP (mem_FP_comp (f := pairFst) (g := MatrixMoment.EntryBits.colIndex) pairFst_mem_FP MatrixMoment.EntryBits.colIndex_mem_FP) HS)))

def momentWriter (F : Parameters) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child F original (birth F ∘ original) .momentPower (momentReader F)

theorem momentWriter_FP (F : Parameters) (a : IntegralCriticalHistoryTask.Access F) : momentWriter F ∈ FP :=
  child_FP F a original original_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary F a))).comp original_FP)
    .momentPower _ (momentReader_FP F a)

theorem momentReader_packet (F : Parameters) (p : List Bool) (i : ℕ) :
    momentReader F (pair p (BinaryNatCode.encode i)) =
      if i = 1 then basisRowCode p else if i = 2 then basisColCode p else
      if i = 11 then MatrixMoment.EntryBits.rowIndex p else if i = 12 then MatrixMoment.EntryBits.colIndex p else
      BinaryNatCode.encode (RankedHistoryFields.get (numericCap F) 16 (original p) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits i
  simp only [momentReader, momentSaved, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem momentWriter_get (F : Parameters) (p : List Bool) (f : Field) :
    get F f (momentWriter F p) =
      if f = .row then min (Nat.fromBitsLE (basisRowCode p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .col then min (Nat.fromBitsLE (basisColCode p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .slot11 then min (Nat.fromBitsLE (MatrixMoment.EntryBits.rowIndex p)) (numericCap F (RankedHistoryTask.root (original p))) else
      if f = .slot12 then min (Nat.fromBitsLE (MatrixMoment.EntryBits.colIndex p)) (numericCap F (RankedHistoryTask.root (original p))) else
      get F f (original p) := by
  have H := get_le F f (original p)
  rw [momentWriter, IntegralCriticalHistoryTask.child_get, momentReader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  all_goals exact min_eq_left H

theorem momentWriter_root (F : Parameters) (p : List Bool) :
    RankedHistoryTask.root (momentWriter F p) = RankedHistoryTask.root (original p) :=
  child_root F _ _ _ _ p

theorem momentWriter_birth (F : Parameters) (p : List Bool) : birth F (momentWriter F p) = birth F (original p) := by
  unfold momentWriter IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem momentWriter_phase (F : Parameters) (p : List Bool) : phase (momentWriter F p) = 22 :=
  IntegralCriticalFlatMatrixQuery.child_phase F _ _ .momentPower _ p

theorem momentWriter_modulus (F : Parameters) (p : List Bool) : modulus F (momentWriter F p) = modulus F (original p) := by
  unfold modulus
  rw [momentWriter_get]
  rfl

theorem momentWriter_lower_rank (F : Parameters) (p : List Bool)
    (hp : 22 < phase (original p)) : rank F (momentWriter F p) < rank F (original p) :=
  child_lower_phase F original _ .momentPower _ p rfl hp

theorem momentWriter_tasks (F : Parameters) (r p : List Bool)
    (hp : Tasks F r (original p)) : Tasks F r (momentWriter F p) :=
  child_tasks F original _ .momentPower _ r p hp (min_le_right _ _)

theorem momentWriter_length (F : Parameters) (p : List Bool) :
    (momentWriter F p).length ≤ wordBudget F (original p) :=
  child_length F original _ .momentPower _ p (min_le_right _ _)

end LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery

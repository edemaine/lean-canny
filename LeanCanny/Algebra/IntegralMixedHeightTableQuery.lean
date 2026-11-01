/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullOldHeightReplies
/-! # Fresh retained-reference queries for physical and virtual affine heights -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightTableQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def radix (P : Parameters) (q : List Bool) := 2 ^ P.width (RankedHistoryTask.root q)
def oldRow (P : Parameters) (q : List Bool) :=
  (if get P .slot15 q = 1 then get P .row q else get P .row q / radix P q) % IntegralMixedOldHeightBits.dimension P q
def oldCol (P : Parameters) (q : List Bool) :=
  (if get P .slot15 q = 1 then get P .col q else get P .col q / radix P q) % IntegralMixedOldHeightBits.dimension P q

theorem radix_binary (P : Parameters) (a : Access P) : BinaryFn (radix P) :=
  (BinaryFn.const 2).powUnary (a.width.comp RankedHistoryTask.root_FP)

theorem oldRow_binary (P : Parameters) (a : Access P) : BinaryFn (oldRow P) :=
  (BinaryFn.ite ((get_binary P a .slot15).eq (BinaryFn.const 1)) (get_binary P a .row)
    ((get_binary P a .row).div (radix_binary P a))).mod (IntegralMixedOldHeightBits.dimension_binary P a)

theorem oldCol_binary (P : Parameters) (a : Access P) : BinaryFn (oldCol P) :=
  (BinaryFn.ite ((get_binary P a .slot15).eq (BinaryFn.const 1)) (get_binary P a .col)
    ((get_binary P a .col).div (radix_binary P a))).mod (IntegralMixedOldHeightBits.dimension_binary P a)

theorem oldRow_le (P : Parameters) (q : List Bool) : oldRow P q ≤ numericCap P (RankedHistoryTask.root q) := by
  unfold oldRow
  apply (Nat.mod_le _ _).trans
  split_ifs
  · exact get_le P .row q
  · exact (Nat.div_le_self _ _).trans (get_le P .row q)

theorem oldCol_le (P : Parameters) (q : List Bool) : oldCol P q ≤ numericCap P (RankedHistoryTask.root q) := by
  unfold oldCol
  apply (Nat.mod_le _ _).trans
  split_ifs
  · exact get_le P .col q
  · exact (Nat.div_le_self _ _).trans (get_le P .col q)

def reader (P : Parameters) (z : List Bool) : List Bool :=
  let q := pairFst (pairFst z)
  let f := Nat.fromBitsLE (pairSnd z)
  if f = Field.sourceIndex.code then pairSnd (pairFst z) else
  if f = Field.row.code then BinaryNatCode.encode (oldRow P q) else
  if f = Field.col.code then BinaryNatCode.encode (oldCol P q) else
  if f = Field.slot14.code then [] else
  RankedHistoryFields.read (numericCap P) 16 (pair q (pairSnd z))

theorem reader_FP (P : Parameters) (a : Access P) : reader P ∈ FP := by
  have HQ := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have HS := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have HR : BinaryFn (fun z => oldRow P (pairFst (pairFst z))) := (oldRow_binary P a).comp HQ
  have HT : BinaryFn (fun z => oldCol P (pairFst (pairFst z))) := (oldCol_binary P a).comp HQ
  have HC := mem_FP_comp (mem_FP_pair HQ pairSnd_mem_FP) (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.sourceIndex.code)).ite_mem_FP HS
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.row.code)).ite_mem_FP HR.bits_mem_FP
      (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.col.code)).ite_mem_FP HT.bits_mem_FP
        (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot14.code)).ite_mem_FP (constFn_mem_FP []) HC)))

def writer (P : Parameters) := child P pairFst (birth P ∘ pairFst) .clearedHeight (reader P)

theorem writer_FP (P : Parameters) (a : Access P) : writer P ∈ FP :=
  child_FP P a pairFst pairFst_mem_FP _ ((BinaryFn.ofUnary (IntegralMixedOldHeightBits.birth_unary P a)).comp pairFst_mem_FP)
    .clearedHeight _ (reader_FP P a)

theorem reader_packet (P : Parameters) (q : List Bool) (i : ℕ) (f : Field) :
    reader P (pair (pair q (BinaryNatCode.encode i)) (BinaryNatCode.encode f.code)) =
      BinaryNatCode.encode (if f = .sourceIndex then i else if f = .row then oldRow P q else
        if f = .col then oldCol P q else if f = .slot14 then 0 else get P f q) := by
  have HF : Nat.fromBitsLE (BinaryNatCode.encode f.code) = f.code := Nat.fromBitsLE_bits _
  simp only [reader, pairFst_pair, pairSnd_pair, HF]
  rw [RankedHistoryFields.read_packet]
  cases f <;> simp only [Field.code, reduceCtorEq, ite_true, ite_false, Nat.reduceEqDiff]
  all_goals rfl

theorem writer_get (P : Parameters) (q : List Bool) (i : ℕ) (f : Field) :
    get P f (writer P (pair q (BinaryNatCode.encode i))) =
      if f = .sourceIndex then min i (numericCap P (RankedHistoryTask.root q)) else
      if f = .row then oldRow P q else if f = .col then oldCol P q else
      if f = .slot14 then 0 else get P f q := by
  rw [writer, child_get, reader_packet]
  cases f <;> simp only [reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.zero_min, pairFst_pair]
  · exact min_eq_left (get_le P .modulus q)
  · exact min_eq_left (oldRow_le P q)
  · exact min_eq_left (oldCol_le P q)
  all_goals exact min_eq_left (get_le P _ q)

theorem writer_root (P : Parameters) (q : List Bool) (i : ℕ) :
    RankedHistoryTask.root (writer P (pair q (BinaryNatCode.encode i))) = RankedHistoryTask.root q := by
  simpa only [writer, pairFst_pair] using child_root P pairFst (birth P ∘ pairFst) .clearedHeight (reader P) (pair q (BinaryNatCode.encode i))

theorem writer_birth (P : Parameters) (q : List Bool) (i : ℕ) :
    birth P (writer P (pair q (BinaryNatCode.encode i))) = birth P q := by
  unfold writer child
  rw [RankedHistoryFields.flatten_eq_pack]
  simp only [Function.comp_apply, pairFst_pair]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_modulus (P : Parameters) (q : List Bool) (i : ℕ) :
    modulus P (writer P (pair q (BinaryNatCode.encode i))) = modulus P q := by
  unfold modulus
  rw [writer_get]
  rfl

theorem writer_routine (P : Parameters) (q : List Bool) (i : ℕ) :
    IntegralMixedRoutineTaskBits.routine P (writer P (pair q (BinaryNatCode.encode i))) = 0 := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [writer_get]
  rfl

theorem writer_phase (P : Parameters) (q : List Bool) (i : ℕ) : phase (writer P (pair q (BinaryNatCode.encode i))) = 2 :=
  IntegralCriticalFlatMatrixQuery.child_phase P pairFst _ .clearedHeight _ _

theorem writer_frame (P : Parameters) (q : List Bool) (i : ℕ)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 0) (hp : phase q = 4) :
    IntegralMixedRoutineTaskBits.Frame P q (writer P (pair q (BinaryNatCode.encode i))) := by
  refine ⟨writer_root P q i, ?_, ?_⟩
  · have HB : birth P q ≤ birthCap P (RankedHistoryTask.root q) := min_le_right _ _
    have HC := child_length P pairFst (birth P ∘ pairFst) .clearedHeight (reader P)
      (pair q (BinaryNatCode.encode i)) (by simpa only [Function.comp_apply, pairFst_pair] using HB)
    simpa only [writer, pairFst_pair] using HC
  · apply IntegralMixedRoutineTaskBits.lower_phase P q _ (writer_birth P q i)
    · rw [writer_routine, hr]
    · rw [writer_phase, hp]; decide

end LeanCanny.Algebra.IntegralMixedHeightTableQueryBits

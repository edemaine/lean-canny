/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueFieldQuery
public import LeanCanny.Algebra.IntegralPowerProductSpace
/-! # Fresh coefficient requests retain the source and both old basis labels -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoefficientQueryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedRoutineTaskBits (Routine)
set_option backward.isDefEq.respectTransparency false

/-- The packet is `pair parent (pair coefficient (pair row col))`. -/
def reader (P : Parameters) (r : Routine) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.slot14.code then BinaryNatCode.encode r.code else
  if Nat.fromBitsLE (pairSnd z) = Field.row.code then IntegralPowerProductBits.rowWord (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = Field.col.code then IntegralPowerProductBits.colWord (pairFst z) else
  if Nat.fromBitsLE (pairSnd z) = Field.coefficient.code then IntegralPowerProductBits.factorWord (pairFst z) else
    RankedHistoryFields.read (numericCap P) 16 (pair (pairFst (pairFst z)) (pairSnd z))

theorem reader_FP (P : Parameters) (a : Access P) (r : Routine) : reader P r ∈ FP := by
  have HI : BinaryFn (fun z => Nat.fromBitsLE (pairSnd z)) := BinaryFn.fromBits pairSnd_mem_FP
  have HD := mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))
  exact (HI.eq (BinaryFn.const Field.slot14.code)).ite_mem_FP (constFn_mem_FP (BinaryNatCode.encode r.code))
    ((HI.eq (BinaryFn.const Field.row.code)).ite_mem_FP
      (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.rowWord) pairFst_mem_FP IntegralPowerProductBits.rowWord_FP)
      ((HI.eq (BinaryFn.const Field.col.code)).ite_mem_FP
        (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.colWord) pairFst_mem_FP IntegralPowerProductBits.colWord_FP)
        ((HI.eq (BinaryFn.const Field.coefficient.code)).ite_mem_FP
          (mem_FP_comp (f := pairFst) (g := IntegralPowerProductBits.factorWord) pairFst_mem_FP IntegralPowerProductBits.factorWord_FP) HD)))

def writer (P : Parameters) (r : Routine) (p : Phase) : List Bool → List Bool :=
  child P pairFst (birth P ∘ pairFst) p (reader P r)

theorem writer_FP (P : Parameters) (a : Access P) (r : Routine) (p : Phase) : writer P r p ∈ FP :=
  child_FP P a pairFst pairFst_mem_FP _
    ((BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))).comp pairFst_mem_FP)
    p _ (reader_FP P a r)

theorem writer_root (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    RankedHistoryTask.root (writer P r p z) = RankedHistoryTask.root (pairFst z) := child_root P _ _ _ _ z

theorem writer_birth (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    birth P (writer P r p z) = birth P (pairFst z) := by
  unfold writer child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem writer_phase (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) : phase (writer P r p z) = p.code :=
  IntegralCriticalFlatMatrixQuery.child_phase P pairFst _ p _ z

theorem reader_packet (P : Parameters) (r : Routine) (z : List Bool) (i : ℕ) :
    reader P r (pair z (BinaryNatCode.encode i)) =
      if i = Field.slot14.code then BinaryNatCode.encode r.code else
      if i = Field.row.code then IntegralPowerProductBits.rowWord z else
      if i = Field.col.code then IntegralPowerProductBits.colWord z else
      if i = Field.coefficient.code then IntegralPowerProductBits.factorWord z else
        BinaryNatCode.encode (RankedHistoryFields.get (numericCap P) 16 (pairFst z) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits _
  simp only [reader, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem writer_get (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) (f : Field) :
    get P f (writer P r p z) =
      if f = .slot14 then r.code else
      if f = .row then min (Nat.fromBitsLE (IntegralPowerProductBits.rowWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .col then min (Nat.fromBitsLE (IntegralPowerProductBits.colWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f = .coefficient then min (Nat.fromBitsLE (IntegralPowerProductBits.factorWord z)) (numericCap P (RankedHistoryTask.root (pairFst z))) else
        get P f (pairFst z) := by
  rw [writer, child_get, reader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  case slot14 => exact min_eq_left ((Nat.le_of_lt_succ r.code_lt).trans (IntegralMixedRoutineTaskBits.routine_cap P _))
  all_goals exact min_eq_left (RankedHistoryFields.get_le (numericCap P) 16 (pairFst z) _)

theorem writer_routine (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (writer P r p z) = r.code := by
  rw [IntegralMixedRoutineTaskBits.routine, writer_get, ite_eq_left rfl]
  exact min_eq_left (Nat.le_of_lt_succ r.code_lt)

theorem writer_saved (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (writer P r p z) = IntegralMixedVirtualTaskBits.saved P (pairFst z) := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact writer_root P r p z
  · exact writer_birth P r p z
  · simp only [writer_get, reduceCtorEq, ite_false]

theorem writer_modulus (P : Parameters) (r : Routine) (p : Phase) (z : List Bool) :
    modulus P (writer P r p z) = modulus P (pairFst z) := by
  unfold modulus
  rw [writer_get]
  rfl

theorem writer_frame (P : Parameters) (r : Routine) (p : Phase) (z : List Bool)
    (hr : r.code < IntegralMixedRoutineTaskBits.routine P (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (writer P r p z) :=
  ⟨writer_root P r p z, child_length P pairFst (birth P ∘ pairFst) p _ z (min_le_right _ _),
    IntegralMixedRoutineTaskBits.lower_routine P _ _ (writer_birth P r p z) (by rw [writer_routine]; exact hr)⟩

end LeanCanny.Algebra.IntegralMixedCoefficientQueryBits

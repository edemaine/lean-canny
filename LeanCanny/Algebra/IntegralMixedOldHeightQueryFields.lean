/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedOldHeightQuery
/-! # Exact bounded-field readbacks of the fresh old-height companion child -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedOldHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedOldBankCofactorBits (Routing)
set_option backward.isDefEq.respectTransparency false

theorem reader_packet (P : Parameters) (R : Routing) (q : List Bool) (f : Field) :
    reader P R (pair q (BinaryNatCode.encode f.code)) = BinaryNatCode.encode
      (if f = .modulus then get P .modulus q else
      if f = .row then get P .row q / radix P q else
      if f = .col then get P .col q / radix P q else
      if f = .slot13 then R.coordinate (packet P q) else
      if f = .slot14 then 6 else
      if f = .slot15 then R.context (packet P q) else 0) := by
  cases f <;> simp only [reader, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Field.code, reduceCtorEq, ite_true, ite_false, Nat.reduceEqDiff, Nat.zero_bits]
  all_goals rfl

theorem writer_get (P : Parameters) (R : Routing) (q : List Bool) (f : Field) :
    get P f (writer P R q) =
      if f = .modulus then get P .modulus q else
      if f = .row then get P .row q / radix P q else
      if f = .col then get P .col q / radix P q else
      if f = .slot13 then min (R.coordinate (packet P q)) (numericCap P (RankedHistoryTask.root q)) else
      if f = .slot14 then 6 else
      if f = .slot15 then min (R.context (packet P q)) (numericCap P (RankedHistoryTask.root q)) else 0 := by
  rw [writer, child_get, reader_packet]
  cases f <;> simp only [reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · exact min_eq_left (get_le P .modulus q)
  · exact min_eq_left ((Nat.div_le_self _ _).trans (get_le P .row q))
  · exact min_eq_left ((Nat.div_le_self _ _).trans (get_le P .col q))
  all_goals try rfl
  exact min_eq_left (IntegralMixedRoutineTaskBits.routine_cap P (RankedHistoryTask.root q))

theorem writer_modulus (P : Parameters) (R : Routing) (q : List Bool) : modulus P (writer P R q) = modulus P q := by
  unfold modulus
  rw [writer_get]
  rfl

theorem writer_routine (P : Parameters) (R : Routing) (q : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (writer P R q) = 6 := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [writer_get]
  rfl

theorem writer_row (P : Parameters) (R : Routing) (q : List Bool) :
    get P .row (writer P R q) = get P .row q / radix P q := by rw [writer_get]; rfl

theorem writer_col (P : Parameters) (R : Routing) (q : List Bool) :
    get P .col (writer P R q) = get P .col q / radix P q := by rw [writer_get]; rfl

theorem writer_context (P : Parameters) (R : Routing) (q : List Bool)
    (h : R.context (packet P q) ≤ numericCap P (RankedHistoryTask.root q)) :
    get P .slot15 (writer P R q) = R.context (packet P q) := by
  rw [writer_get]
  exact min_eq_left h

theorem writer_coordinate (P : Parameters) (R : Routing) (q : List Bool)
    (h : R.coordinate (packet P q) ≤ numericCap P (RankedHistoryTask.root q)) :
    get P .slot13 (writer P R q) = R.coordinate (packet P q) := by
  rw [writer_get]
  exact min_eq_left h

end LeanCanny.Algebra.IntegralMixedOldHeightBits

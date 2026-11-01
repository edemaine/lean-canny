/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationTopQueries
/-! # The leading-matrix leaf asks the actual raw cut at its selected degree -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
set_option backward.isDefEq.respectTransparency false

noncomputable def rawCutValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedCutSource.source F).coefficient (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (get P .row q) (get P .col q) : ZMod (modulus P q))

def rawReader (P : Parameters) (F : Family) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.coefficient.code then
    BinaryNatCode.encode (F.degree (IntegralMixedVirtualTaskBits.saved P (pairFst z)))
  else IntegralMixedRoutineTaskBits.reader P .rawFactor z

theorem rawReader_FP (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : rawReader P F ∈ FP := by
  have HD : BinaryFn (fun z => F.degree (IntegralMixedVirtualTaskBits.saved P (pairFst z))) :=
    hd.comp (mem_FP_comp pairFst_mem_FP (IntegralMixedVirtualTaskBits.saved_FP P a))
  exact ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.coefficient.code)).ite_mem_FP
    HD.bits_mem_FP (IntegralMixedRoutineTaskBits.reader_FP P a .rawFactor)

def rawQuery (P : Parameters) (F : Family) : List Bool → List Bool :=
  child P id (birth P) .companion (rawReader P F)

theorem rawQuery_FP (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : rawQuery P F ∈ FP :=
  child_FP P a id id_mem_FP _
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (birthCap_unary P a))) .companion _ (rawReader_FP P a F hd)

theorem rawReader_packet (P : Parameters) (F : Family) (q : List Bool) (i : ℕ) :
    rawReader P F (pair q (BinaryNatCode.encode i)) =
      if i = Field.coefficient.code then BinaryNatCode.encode (F.degree (IntegralMixedVirtualTaskBits.saved P q)) else
      if i = Field.slot14.code then BinaryNatCode.encode 4 else
        BinaryNatCode.encode (RankedHistoryFields.get (numericCap P) 16 q i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits _
  simp only [rawReader, IntegralMixedRoutineTaskBits.reader, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]
  rfl

theorem rawQuery_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (rawQuery P F q) = RankedHistoryTask.root q := child_root P _ _ _ _ q

theorem rawQuery_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (rawQuery P F q) = birth P q := by
  unfold rawQuery child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem rawQuery_phase (P : Parameters) (F : Family) (q : List Bool) : phase (rawQuery P F q) = 26 :=
  IntegralCriticalFlatMatrixQuery.child_phase P id (birth P) .companion _ q

theorem rawQuery_get (P : Parameters) (F : Family) (q : List Bool) (f : Field) :
    get P f (rawQuery P F q) =
      if f = .coefficient then min (F.degree (IntegralMixedVirtualTaskBits.saved P q)) (numericCap P (RankedHistoryTask.root q)) else
      if f = .slot14 then 4 else get P f q := by
  rw [rawQuery, child_get, rawReader_packet]
  cases f <;> norm_num only [id_eq, Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  case slot14 => exact min_eq_left ((by decide : 4 ≤ 6).trans (IntegralMixedRoutineTaskBits.routine_cap P _))
  all_goals exact min_eq_left (RankedHistoryFields.get_le (numericCap P) 16 q _)

theorem rawQuery_routine (P : Parameters) (F : Family) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (rawQuery P F q) = 4 := by
  unfold IntegralMixedRoutineTaskBits.routine
  rw [rawQuery_get]
  rfl

theorem rawQuery_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (rawQuery P F q) = IntegralMixedVirtualTaskBits.saved P q := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact rawQuery_root P F q
  · exact rawQuery_birth P F q
  · simp only [rawQuery_get, reduceCtorEq, ite_false]

theorem rawQuery_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (rawQuery P F q) = modulus P q := by
  unfold modulus
  rw [rawQuery_get]
  rfl

theorem cut_degree_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    F.degree (IntegralMixedVirtualTaskBits.saved P q) ≤ numericCap P (RankedHistoryTask.root q) := by
  have H := (F.degree_bound (IntegralMixedVirtualTaskBits.saved P q)).trans (F.scalar_cap (IntegralMixedVirtualTaskBits.saved P q))
  rw [g.width] at H
  exact H.trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem rawQuery_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    rawCutValue P F (rawQuery P F q) = value P F q := by
  have HC : get P .coefficient (rawQuery P F q) = F.degree (IntegralMixedVirtualTaskBits.saved P q) := by
    rw [rawQuery_get]
    exact min_eq_left (cut_degree_cap P F g q)
  unfold rawCutValue
  rw [rawQuery_saved, rawQuery_modulus, HC, rawQuery_get, rawQuery_get]
  simp only [reduceCtorEq, ite_false]
  rw [IntegralMixedCutSource.source_coefficient, ite_eq_left (Nat.le_refl _)]
  rfl

theorem rawQuery_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 5) : IntegralMixedRoutineTaskBits.Frame P q (rawQuery P F q) := by
  refine ⟨rawQuery_root P F q, ?_, ?_⟩
  · exact child_length P id (birth P) .companion _ q (min_le_right _ _)
  · exact IntegralMixedRoutineTaskBits.lower_routine P q _ (rawQuery_birth P F q)
      (by rw [rawQuery_routine, hr]; decide)

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

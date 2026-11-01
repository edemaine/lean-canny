/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueFieldQuery
public import LeanCanny.Algebra.IntegralMixedValueHomogeneousSource

/-! # Homogeneous value rows request actual restored or critical coefficients

Routine two, phase 22, selects a restored original row at phase 21 or an
actual virtual coordinate coefficient in routine one, phase 25. The saved
parent and its source context remain unchanged. Coordinate and coefficient
fields have explicit unclipped readbacks; the native request guard supplies
their local degree bounds, independently of any integer norm degree.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueHomogeneousQueries
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

def packet (P : Parameters) (q : List Bool) : List Bool :=
  MacaulayFullBoxBits.entryPacket q (get P .slot8 q) (get P .target q) (get P .row q) (get P .col q)

theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (get_binary P a .slot8).bits_mem_FP
    (mem_FP_pair (get_binary P a .target).bits_mem_FP
      (mem_FP_pair (get_binary P a .row).bits_mem_FP (get_binary P a .col).bits_mem_FP)))

noncomputable abbrev parameters (P : Parameters) (F : Family) :=
  IntegralMixedValueHomogeneousSource.parameters (IntegralMixedVirtualTaskBits.family P F)

theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    HomogeneousSystemCoefficientRequest.Controls (parameters P F) :=
  IntegralMixedValueHomogeneousSource.controls _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)

noncomputable def originalTarget (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  Nat.fromBitsLE (HomogeneousSystemCoefficientRequest.stripped (parameters P F) (packet P q))

noncomputable def coordinateCoefficient (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  HomogeneousSystemCoefficientRequest.coefficient (parameters P F) (packet P q)

theorem originalTarget_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (originalTarget P F) := by
  have HS : (fun q => HomogeneousSystemCoefficientRequest.stripped (parameters P F) (packet P q)) ∈ FP :=
    mem_FP_comp (f := packet P) (g := HomogeneousSystemCoefficientRequest.stripped (parameters P F))
      (packet_FP P a) (HomogeneousSystemCoefficientRequest.stripped_FP _ (controls P a F h))
  exact BinaryFn.fromBits HS

theorem coordinateCoefficient_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    BinaryFn (coordinateCoefficient P F) :=
  (HomogeneousSystemCoefficientRequest.coefficient_binary _ (controls P a F h)).comp (packet_FP P a)

noncomputable def originalTask (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .pscEntry .momentEntry .target (originalTarget P F)

def coordinateBase (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P id .critical .criticalCoefficient .slot13 (fun q => get P .slot8 q - 1)

noncomputable def coordinateTask (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (coordinateBase P) .critical .criticalCoefficient .coefficient
    (coordinateCoefficient P F)

noncomputable def query (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  if get P .slot8 q = 0 then originalTask P F q else coordinateTask P F q

theorem originalTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : originalTask P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (originalTarget_binary P a F h)

theorem coordinateBase_FP (P : Parameters) (a : Access P) : coordinateBase P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ ((get_binary P a .slot8).sub (BinaryFn.const 1))

theorem coordinateTask_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : coordinateTask P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (coordinateBase_FP P a) _ _ _ _ (coordinateCoefficient_binary P a F h)

theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  ((get_binary P a .slot8).eq (BinaryFn.const 0)).ite_mem_FP (originalTask_FP P a F h) (coordinateTask_FP P a F h)

theorem coordinateBase_root (P : Parameters) (q : List Bool) :
    RankedHistoryTask.root (coordinateBase P q) = RankedHistoryTask.root q :=
  IntegralMixedValueFieldQuery.query_root P id _ _ _ _ q

theorem coordinateTask_get (P : Parameters) (F : Family) (q : List Bool) (f : Field) :
    get P f (coordinateTask P F q) =
      if f = .slot14 then 1 else
      if f = .coefficient then min (coordinateCoefficient P F q) (numericCap P (RankedHistoryTask.root q)) else
      if f = .slot13 then min (get P .slot8 q - 1) (numericCap P (RankedHistoryTask.root q)) else get P f q := by
  rw [coordinateTask, IntegralMixedValueFieldQuery.query_get, coordinateBase_root]
  rw [coordinateBase, IntegralMixedValueFieldQuery.query_get]
  cases f <;> rfl

theorem coordinateTask_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (coordinateTask P F q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P (coordinateBase P) _ _ _ _ q).trans (coordinateBase_root P q)

theorem coordinateTask_birth (P : Parameters) (F : Family) (q : List Bool) :
    birth P (coordinateTask P F q) = birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P (coordinateBase P) _ _ _ _ q).trans
    (IntegralMixedValueFieldQuery.query_birth P id _ _ _ _ q)

theorem coordinateTask_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (coordinateTask P F q) = IntegralMixedVirtualTaskBits.saved P q := by
  apply IntegralMixedVirtualTaskBits.saved_invariance
  · exact coordinateTask_root P F q
  · exact coordinateTask_birth P F q
  · simp only [coordinateTask_get, reduceCtorEq, ite_false]

theorem coordinateTask_modulus (P : Parameters) (F : Family) (q : List Bool) :
    modulus P (coordinateTask P F q) = modulus P q := by
  unfold modulus
  simp only [coordinateTask_get, reduceCtorEq, ite_false]

theorem coordinateTask_value (P : Parameters) (F : Family) (q : List Bool)
    (hj : get P .slot8 q - 1 ≤ numericCap P (RankedHistoryTask.root q))
    (hk : coordinateCoefficient P F q ≤ numericCap P (RankedHistoryTask.root q)) :
    (IntegralMixedVirtualTaskBits.source P F).value (coordinateTask P F q) =
      residueBits (matrixCoefficient F (IntegralMixedVirtualTaskBits.saved P q)
        (get P .slot8 q - 1) (coordinateCoefficient P F q) (get P .row q) (get P .col q) : ZMod (modulus P q)) := by
  rw [IntegralMixedVirtualTaskBits.value_snapshot, coordinateTask_saved, coordinateTask_modulus]
  simp only [IntegralMixedVirtualTaskBits.coordinate, coordinateTask_get, reduceCtorEq, ite_true, ite_false,
    min_eq_left hj, min_eq_left hk]

theorem coordinateTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) :
    IntegralMixedRoutineTaskBits.Frame P q (coordinateTask P F q) := by
  refine ⟨coordinateTask_root P F q, ?_, ?_⟩
  · have HB := IntegralMixedValueFieldQuery.query_length P (coordinateBase P) .critical
      .criticalCoefficient .coefficient (coordinateCoefficient P F) q
    have HW : wordBudget P (coordinateBase P q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [coordinateBase_root]
    exact HB.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (coordinateTask_birth P F q)
    rw [IntegralMixedRoutineTaskBits.routine, coordinateTask_get, hr]
    simp only [reduceCtorEq, ite_true]
    decide

theorem originalTask_get (P : Parameters) (F : Family) (q : List Bool) (f : Field) :
    get P f (originalTask P F q) =
      if f = .slot14 then 2 else
      if f = .target then min (originalTarget P F q) (numericCap P (RankedHistoryTask.root q)) else get P f q :=
  IntegralMixedValueFieldQuery.query_get P id .pscEntry .momentEntry .target (originalTarget P F) q f

theorem originalTask_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (originalTask P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  IntegralMixedValueFieldQuery.query_saved P id .pscEntry .momentEntry .target (originalTarget P F) q (by decide)

theorem originalTask_modulus (P : Parameters) (F : Family) (q : List Bool) :
    modulus P (originalTask P F q) = modulus P q :=
  IntegralMixedValueFieldQuery.query_modulus P id .pscEntry .momentEntry .target (originalTarget P F) q (by decide)

theorem originalTask_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 22) :
    IntegralMixedRoutineTaskBits.Frame P q (originalTask P F q) :=
  IntegralMixedValueFieldQuery.query_frame_phase P id .pscEntry .momentEntry .target (originalTarget P F) q hr
    (by rw [show id q = q from rfl, hp]; decide)

theorem query_frame (P : Parameters) (F : Family) (q : List Bool)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 2) (hp : phase q = 22) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  unfold query
  split_ifs
  · exact originalTask_frame P F q hr hp
  · exact coordinateTask_frame P F q hr

end LeanCanny.Algebra.IntegralMixedValueHomogeneousQueries

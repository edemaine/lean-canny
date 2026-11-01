/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRoutineTask
/-! # Fresh routine queries selecting a producer's own source context

A legacy controller packet names a saved parent through an explicit native
projection. The output stores that parent's ROOT once, the requested birth,
phase and routine, and fresh coordinate/context fields 13/15. It retains no
nested parent packet. Earlier-prefix queries can select any routine/context.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRoutineContextQuery
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedRoutineTaskBits (Routine)
set_option backward.isDefEq.respectTransparency false

def copy (P : Parameters) (parent : List Bool → List Bool) (z : List Bool) : List Bool :=
  RankedHistoryFields.read (numericCap P) 16 (pair (parent (pairFst z)) (pairSnd z))

def reader (P : Parameters) (parent : List Bool → List Bool) (r : Routine)
    (coordinate context : List Bool → ℕ) (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd z) = Field.slot13.code then BinaryNatCode.encode (coordinate (pairFst z)) else
  if Nat.fromBitsLE (pairSnd z) = Field.slot14.code then BinaryNatCode.encode r.code else
  if Nat.fromBitsLE (pairSnd z) = Field.slot15.code then BinaryNatCode.encode (context (pairFst z)) else copy P parent z

theorem copy_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool) (hp : parent ∈ FP) : copy P parent ∈ FP :=
  mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP hp) pairSnd_mem_FP)
    (RankedHistoryFields.read_FP (numericCap P) 16 (numericCap_binary P a))

theorem reader_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool) (hp : parent ∈ FP)
    (r : Routine) (coordinate context : List Bool → ℕ) (hc : BinaryFn coordinate) (hx : BinaryFn context) : reader P parent r coordinate context ∈ FP :=
  ((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot13.code)).ite_mem_FP
    (mem_FP_comp pairFst_mem_FP hc.bits_mem_FP)
    (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot14.code)).ite_mem_FP
      (constFn_mem_FP (BinaryNatCode.encode r.code))
      (((BinaryFn.fromBits pairSnd_mem_FP).eq (BinaryFn.const Field.slot15.code)).ite_mem_FP
        (mem_FP_comp pairFst_mem_FP hx.bits_mem_FP) (copy_FP P a parent hp)))

def query (P : Parameters) (parent : List Bool → List Bool) (birth : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) : List Bool → List Bool :=
  child P parent birth p (reader P parent r coordinate context)

theorem query_FP (P : Parameters) (a : Access P) (parent : List Bool → List Bool) (hp : parent ∈ FP)
    (b : List Bool → ℕ) (hb : BinaryFn b) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (hc : BinaryFn coordinate) (hx : BinaryFn context) :
    query P parent b r p coordinate context ∈ FP :=
  child_FP P a parent hp b hb p _ (reader_FP P a parent hp r coordinate context hc hx)

theorem reader_packet (P : Parameters) (parent : List Bool → List Bool) (r : Routine)
    (coordinate context : List Bool → ℕ) (q : List Bool) (i : ℕ) :
    reader P parent r coordinate context (pair q (BinaryNatCode.encode i)) =
      if i = Field.slot13.code then BinaryNatCode.encode (coordinate q) else
      if i = Field.slot14.code then BinaryNatCode.encode r.code else
      if i = Field.slot15.code then BinaryNatCode.encode (context q) else
        BinaryNatCode.encode (RankedHistoryFields.get (numericCap P) 16 (parent q) i) := by
  have HI : Nat.fromBitsLE (BinaryNatCode.encode i) = i := Nat.fromBitsLE_bits _
  simp only [reader, copy, pairFst_pair, pairSnd_pair, HI]
  rw [RankedHistoryFields.read_packet]

theorem query_root (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) :
    RankedHistoryTask.root (query P parent b r p coordinate context q) = RankedHistoryTask.root (parent q) := child_root P parent b p _ q

theorem query_birth (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hb : b q ≤ birthCap P (RankedHistoryTask.root (parent q))) :
    birth P (query P parent b r p coordinate context q) = b q := by
  unfold query child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ hb

theorem query_phase (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) : phase (query P parent b r p coordinate context q) = p.code :=
  IntegralCriticalFlatMatrixQuery.child_phase P parent b p _ q

theorem query_get (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (f : Field) :
    get P f (query P parent b r p coordinate context q) =
      if f = .slot13 then min (coordinate q) (numericCap P (RankedHistoryTask.root (parent q))) else
      if f = .slot14 then r.code else
      if f = .slot15 then min (context q) (numericCap P (RankedHistoryTask.root (parent q))) else get P f (parent q) := by
  rw [query, child_get, reader_packet]
  cases f <;> norm_num only [Field.code, reduceCtorEq, ite_true, ite_false, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  case slot14 => exact min_eq_left ((Nat.le_of_lt_succ r.code_lt).trans (IntegralMixedRoutineTaskBits.routine_cap P _))
  all_goals exact min_eq_left (RankedHistoryFields.get_le (numericCap P) 16 (parent q) _)

theorem query_routine (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) :
    IntegralMixedRoutineTaskBits.routine P (query P parent b r p coordinate context q) = r.code := by
  rw [IntegralMixedRoutineTaskBits.routine, query_get, ite_eq_right (by decide), ite_eq_left rfl]
  exact min_eq_left (Nat.le_of_lt_succ r.code_lt)

theorem query_other (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (f : Field)
    (hc : f ≠ .slot13) (hr : f ≠ .slot14) (hx : f ≠ .slot15) :
    get P f (query P parent b r p coordinate context q) = get P f (parent q) := by
  rw [query_get, ite_eq_right hc, ite_eq_right hr, ite_eq_right hx]

theorem query_coordinate (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hc : coordinate q ≤ numericCap P (RankedHistoryTask.root (parent q))) :
    get P .slot13 (query P parent b r p coordinate context q) = coordinate q := by
  rw [query_get, ite_eq_left rfl, min_eq_left hc]

theorem query_context (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hx : context q ≤ numericCap P (RankedHistoryTask.root (parent q))) :
    get P .slot15 (query P parent b r p coordinate context q) = context q := by
  rw [query_get, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, min_eq_left hx]

theorem query_modulus (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) :
    modulus P (query P parent b r p coordinate context q) = modulus P (parent q) := by
  unfold modulus
  rw [query_other P parent b r p coordinate context q .modulus (by decide) (by decide) (by decide)]

theorem query_length (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hb : b q ≤ birthCap P (RankedHistoryTask.root (parent q))) :
    (query P parent b r p coordinate context q).length ≤ wordBudget P (parent q) := child_length P parent b p _ q hb

theorem query_frame_birth (P : Parameters) (parent : List Bool → List Bool) (b : List Bool → ℕ) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hb : b q < birth P (parent q)) :
    IntegralMixedRoutineTaskBits.Frame P (parent q) (query P parent b r p coordinate context q) := by
  have HC : b q ≤ birthCap P (RankedHistoryTask.root (parent q)) := hb.le.trans (min_le_right _ _)
  exact ⟨query_root P parent b r p coordinate context q, query_length P parent b r p coordinate context q HC,
    IntegralMixedRoutineTaskBits.lower_birth P (parent q) _ (by rw [query_birth P parent b r p coordinate context q HC]; exact hb)⟩

theorem query_frame_routine (P : Parameters) (parent : List Bool → List Bool) (r : Routine) (p : Phase)
    (coordinate context : List Bool → ℕ) (q : List Bool) (hr : r.code < IntegralMixedRoutineTaskBits.routine P (parent q)) :
    IntegralMixedRoutineTaskBits.Frame P (parent q) (query P parent (birth P ∘ parent) r p coordinate context q) := by
  have HC : (birth P ∘ parent) q ≤ birthCap P (RankedHistoryTask.root (parent q)) := min_le_right _ _
  exact ⟨query_root P parent _ r p coordinate context q, query_length P parent _ r p coordinate context q HC,
    IntegralMixedRoutineTaskBits.lower_routine P (parent q) _ (query_birth P parent _ r p coordinate context q HC)
      (by rw [query_routine]; exact hr)⟩
end LeanCanny.Algebra.IntegralMixedRoutineContextQuery

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalQuery
public import LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery
/-! # A concrete task backend for physical critical arithmetic

The source key records root, scalar mixed-prefix length, and context kind
(slot 15). Slot 13 independently retains the chosen annihilator coordinate.
The routine tag (slot 14) and changing arithmetic fields do not select the
coefficient algebra. No formal digit is added. All phase codes and ordinary arithmetic writers are reused.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalTaskBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits
set_option backward.isDefEq.respectTransparency false

def saved (P : Parameters) (q : List Bool) : List Bool :=
  pair (RankedHistoryTask.root q) (pair (BinaryNatCode.encode (birth P q))
    (BinaryNatCode.encode (get P .slot15 q)))

theorem saved_FP (P : Parameters) (a : Access P) : saved P ∈ FP :=
  mem_FP_pair RankedHistoryTask.root_FP
    (mem_FP_pair (bits_mem_FP (RankedHistoryTask.birth_unary _ (birthCap_unary P a)))
      (get_binary P a .slot15).bits_mem_FP)

def coordinate (P : Parameters) : List Bool → ℕ := get P .slot13

abbrev queries (P : Parameters) := taskQueries P (coordinate P)

noncomputable abbrev family (P : Parameters) (F : Family) := pull F (saved P)
noncomputable abbrev indices (P : Parameters) (F : Family) :=
  IntegralMixedPhysicalQueryBits.indices (family P F) (queries P)
noncomputable abbrev source (P : Parameters) (F : Family) :=
  IntegralMixedPhysicalCriticalBits.source (family P F) (indices P F)
noncomputable abbrev arithmetic (P : Parameters) (F : Family) := (source P F).toEuler

theorem metadata (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    IntegralMixedPhysicalCriticalBits.Metadata (family P F) (indices P F) :=
  IntegralMixedPhysicalQueryBits.metadata _ (pull_metadata F h (saved P) (saved_FP P a))
    (queries P) (task_metadata P a (coordinate P) (get_binary P a .slot13))

noncomputable def access (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) :
    IntegralClearedCriticalBits.Access (source P F) :=
  IntegralMixedPhysicalCriticalBits.criticalAccess (family P F) (indices P F) (metadata P a F h)

theorem saved_invariance (P : Parameters) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hk : get P .slot15 c = get P .slot15 q) : saved P c = saved P q := by
  simp only [saved, hr, hb, hk]

theorem value_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).value q = residueBits
      (matrixCoefficient F (saved P q) (coordinate P q) (get P .coefficient q) (get P .row q) (get P .col q) :
        ZMod (modulus P q)) :=
  IntegralMixedPhysicalQueryBits.value_snapshot (family P F) (queries P) q

theorem value_invariance (P : Parameters) (F : Family) (q c : List Bool)
    (hr : RankedHistoryTask.root c = RankedHistoryTask.root q) (hb : birth P c = birth P q)
    (hk : get P .slot15 c = get P .slot15 q) (hj : coordinate P c = coordinate P q)
    (he : get P .coefficient c = get P .coefficient q) (hi : get P .row c = get P .row q)
    (ht : get P .col c = get P .col q) (hm : modulus P c = modulus P q) :
    (source P F).value c = (source P F).value q := by
  rw [value_snapshot, value_snapshot, saved_invariance P q c hr hb hk, hj, he, hi, ht, hm]

theorem matrix_saved (P : Parameters) (p : Phase) (z : List Bool) :
    saved P (IntegralCriticalFlatMatrixQuery.writer P p z) = saved P (pairFst z) := by
  apply saved_invariance
  · exact IntegralCriticalFlatMatrixQuery.writer_root P p z
  · exact IntegralCriticalFlatMatrixQuery.writer_birth P p z
  · rw [IntegralCriticalFlatMatrixQuery.writer_get]
    rfl

theorem matrix_coordinate (P : Parameters) (p : Phase) (z : List Bool) :
    coordinate P (IntegralCriticalFlatMatrixQuery.writer P p z) = coordinate P (pairFst z) := by
  rw [coordinate, IntegralCriticalFlatMatrixQuery.writer_get]
  rfl

theorem matrix_routine (P : Parameters) (p : Phase) (z : List Bool) :
    get P .slot14 (IntegralCriticalFlatMatrixQuery.writer P p z) = get P .slot14 (pairFst z) := by
  rw [IntegralCriticalFlatMatrixQuery.writer_get]
  rfl

theorem matrix_value (P : Parameters) (F : Family) (p : Phase) (z : List Bool) :
    (source P F).value (IntegralCriticalFlatMatrixQuery.writer P p z) =
      residueBits (matrixCoefficient F (saved P (pairFst z)) (coordinate P (pairFst z))
        (get P .coefficient (pairFst z))
        (min (Nat.fromBitsLE (pairFst (pairSnd z))) (numericCap P (RankedHistoryTask.root (pairFst z))))
        (min (Nat.fromBitsLE (pairSnd (pairSnd z))) (numericCap P (RankedHistoryTask.root (pairFst z)))) :
          ZMod (modulus P (pairFst z))) := by
  rw [value_snapshot, matrix_saved, matrix_coordinate,
    IntegralCriticalFlatMatrixQuery.writer_modulus,
    IntegralCriticalFlatMatrixQuery.writer_get,
    IntegralCriticalFlatMatrixQuery.writer_get,
    IntegralCriticalFlatMatrixQuery.writer_get]
  rfl
end LeanCanny.Algebra.IntegralMixedPhysicalTaskBits

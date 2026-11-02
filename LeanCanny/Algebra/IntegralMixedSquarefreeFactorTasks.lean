/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscUpperSelection
/-! # Two lower-routine tasks for the squarefree scalar product -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeFactorTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical

noncomputable def topRow (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P id .critical .criticalCoefficient .row (fun _ => 0)
noncomputable def topCol (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P (topRow P) .critical .criticalCoefficient .col (fun _ => 0)
noncomputable def top (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (topCol P) .critical .criticalCoefficient .coefficient (IntegralMixedPscEntryBits.degree P F)
noncomputable def determinant (P : Parameters) :=
  IntegralMixedValueFieldQuery.query P id .pscDeterminant .factorPower .target (fun _ => 0)

theorem topRow_FP (P : Parameters) (a : Access P) : topRow P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (BinaryFn.const 0)
theorem topCol_FP (P : Parameters) (a : Access P) : topCol P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (topRow_FP P a) _ _ _ _ (BinaryFn.const 0)
theorem top_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : top P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (topCol_FP P a) _ _ _ _ (IntegralMixedPscEntryBits.degree_binary P a F h)
theorem determinant_FP (P : Parameters) (a : Access P) : determinant P ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (BinaryFn.const 0)

theorem degree_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedPscEntryBits.degree P F q ≤ numericCap P (RankedHistoryTask.root q) :=
  (IntegralMixedValueTaskBounds.coordinateDegree_lt_scalar (IntegralMixedVirtualTaskBits.family P F) q).le.trans
    (IntegralMixedValueTaskBounds.scalar_le_root_cap P F g q)

theorem top_root (P : Parameters) (F : Family) (q : List Bool) :
    RankedHistoryTask.root (top P F q) = RankedHistoryTask.root q := by
  simp only [top, topCol, topRow, IntegralMixedValueFieldQuery.query_root, id_eq]

theorem top_birth (P : Parameters) (F : Family) (q : List Bool) :
    birth P (top P F q) = birth P q := by
  simp only [top, topCol, topRow, IntegralMixedValueFieldQuery.query_birth, id_eq]

theorem top_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (top P F q) = IntegralMixedVirtualTaskBits.saved P q := by
  exact (IntegralMixedValueFieldQuery.query_saved P (topCol P) .critical .criticalCoefficient .coefficient _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_saved P (topRow P) .critical .criticalCoefficient .col _ q (by decide)).trans
      (IntegralMixedValueFieldQuery.query_saved P id .critical .criticalCoefficient .row _ q (by decide)))

theorem top_modulus (P : Parameters) (F : Family) (q : List Bool) :
    modulus P (top P F q) = modulus P q := by
  exact (IntegralMixedValueFieldQuery.query_modulus P (topCol P) .critical .criticalCoefficient .coefficient _ q (by decide)).trans
    ((IntegralMixedValueFieldQuery.query_modulus P (topRow P) .critical .criticalCoefficient .col _ q (by decide)).trans
      (IntegralMixedValueFieldQuery.query_modulus P id .critical .criticalCoefficient .row _ q (by decide)))

theorem determinant_root (P : Parameters) (q : List Bool) :
    RankedHistoryTask.root (determinant P q) = RankedHistoryTask.root q := by
  simp only [determinant, IntegralMixedValueFieldQuery.query_root, id_eq]

theorem determinant_birth (P : Parameters) (q : List Bool) :
    birth P (determinant P q) = birth P q := by
  simp only [determinant, IntegralMixedValueFieldQuery.query_birth, id_eq]

theorem determinant_saved (P : Parameters) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (determinant P q) = IntegralMixedVirtualTaskBits.saved P q := by
  exact IntegralMixedValueFieldQuery.query_saved P id .pscDeterminant .factorPower .target _ q (by decide)

theorem determinant_modulus (P : Parameters) (q : List Bool) :
    modulus P (determinant P q) = modulus P q := by
  exact IntegralMixedValueFieldQuery.query_modulus P id .pscDeterminant .factorPower .target _ q (by decide)

theorem top_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (f : Field) :
    get P f (top P F q) = if f = .slot14 then 1 else if f = .coefficient then IntegralMixedPscEntryBits.degree P F q
      else if f = .row ∨ f = .col then 0 else get P f q := by
  simp only [top, topCol, topRow, IntegralMixedValueFieldQuery.query_get,
    IntegralMixedValueFieldQuery.query_root, id_eq, Nat.zero_min]
  rw [min_eq_left (degree_cap P F g q)]
  cases f <;> rfl

theorem determinant_get (P : Parameters) (q : List Bool) (f : Field) :
    get P f (determinant P q) = if f = .slot14 then 3 else if f = .target then 0 else get P f q := by
  simp only [determinant, IntegralMixedValueFieldQuery.query_get, id_eq, Nat.zero_min]
  cases f <;> rfl

theorem top_frame (P : Parameters) (F : Family) (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 4) :
    IntegralMixedRoutineTaskBits.Frame P q (top P F q) := by
  refine ⟨top_root P F q, ?_, ?_⟩
  · have H := IntegralMixedValueFieldQuery.query_length P (topCol P) .critical .criticalCoefficient .coefficient
      (IntegralMixedPscEntryBits.degree P F) q
    have HW : wordBudget P (topCol P q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      simp only [topCol, topRow, IntegralMixedValueFieldQuery.query_root, id_eq]
    exact H.trans_eq HW
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (top_birth P F q)
    rw [top, IntegralMixedValueFieldQuery.query_routine, hr]
    decide

theorem determinant_frame (P : Parameters) (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 4) :
    IntegralMixedRoutineTaskBits.Frame P q (determinant P q) :=
  IntegralMixedValueFieldQuery.query_frame_routine P id .pscDeterminant .factorPower .target _ q (by change 3 < IntegralMixedRoutineTaskBits.routine P q; rw [hr]; decide)

end LeanCanny.Algebra.IntegralMixedSquarefreeFactorTasks

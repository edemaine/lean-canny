/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSnapshot
public import LeanCanny.Algebra.IntegralMixedValueCoefficientTasks
/-! # Coordinate coefficient requests call the actual virtual critical coefficient -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateCoefficientTasks
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedValueCoefficientTasks
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def choiceBound (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralMixedCoordinateTrailing.ChoiceBound ((IntegralMixedVirtualTaskBits.family P F).spatial q)
    ((IntegralMixedVirtualTaskBits.family P F).rule q)

theorem choiceBound_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (choiceBound P F) :=
  (IntegralMixedValueDeterminantMetadata.coordinateDegree_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)).add (BinaryFn.const 1)

noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (IntegralMixedValueCoefficientTasks.query P F)
    .critical .criticalCoefficient .coefficient (get P .slot8)

theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : query P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (IntegralMixedValueCoefficientTasks.query_FP P a F h)
    _ _ _ _ (get_binary P a .slot8)

theorem query_root (P : Parameters) (F : Family) (q : List Bool) : RankedHistoryTask.root (query P F q) = RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ q).trans (IntegralMixedValueCoefficientTasks.query_root P F q)

theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q) = birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ q).trans (IntegralMixedValueCoefficientTasks.query_birth P F q)

theorem query_phase (P : Parameters) (F : Family) (q : List Bool) : phase (query P F q) = 25 :=
  IntegralMixedValueFieldQuery.query_phase P _ _ _ _ _ q

theorem query_routine (P : Parameters) (F : Family) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (query P F q) = 1 :=
  IntegralMixedValueFieldQuery.query_routine P _ _ _ _ _ q

theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ q (by decide)).trans (IntegralMixedValueCoefficientTasks.query_saved P F q)

theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P _ _ _ _ _ q (by decide)).trans (IntegralMixedValueCoefficientTasks.query_modulus P F q)

theorem query_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hl : Labels P F q) (f : Field) :
    get P f (query P F q) = if f = .slot14 then 1 else if f = .coefficient then get P .slot8 q else
      if f = .col then packedCol P F q else if f = .row then packedRow P F q else get P f q := by
  rw [query, IntegralMixedValueFieldQuery.query_get, IntegralMixedValueCoefficientTasks.query_root,
    min_eq_left (get_le P .slot8 q), IntegralMixedValueCoefficientTasks.query_get P F g q hv hl]
  cases f <;> rfl

theorem query_frame (P : Parameters) (F : Family) (q : List Bool) (hr : IntegralMixedRoutineTaskBits.routine P q = 4) :
    IntegralMixedRoutineTaskBits.Frame P q (query P F q) := by
  refine ⟨query_root P F q, ?_, ?_⟩
  · have he := IntegralMixedValueFieldQuery.query_length P (IntegralMixedValueCoefficientTasks.query P F)
      .critical .criticalCoefficient .coefficient (get P .slot8) q
    have hw : wordBudget P (IntegralMixedValueCoefficientTasks.query P F q) = wordBudget P q := by
      unfold wordBudget RankedHistoryTask.wordBudget
      rw [IntegralMixedValueCoefficientTasks.query_root]
    exact he.trans_eq hw
  · apply IntegralMixedRoutineTaskBits.lower_routine P q _ (query_birth P F q)
    rw [query_routine, hr]
    decide

end LeanCanny.Algebra.IntegralMixedCoordinateCoefficientTasks

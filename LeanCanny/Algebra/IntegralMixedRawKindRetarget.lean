/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindData
/-! # Fresh raw-cut packets restore the immutable creating choice locally -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def first (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P id .rawFactor .companion .slot8
    (fun q => choice F (IntegralMixedVirtualTaskBits.saved P q))
noncomputable def prepare (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (first P F) .rawFactor .companion .slot13
    (fun q => coordinate F (IntegralMixedVirtualTaskBits.saved P q))

theorem first_FP (P : Parameters) (a : Access P) (F : Family) (h : Metadata F) : first P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a id id_mem_FP _ _ _ _ (h.choice.comp (IntegralMixedVirtualTaskBits.saved_FP P a))
theorem prepare_FP (P : Parameters) (a : Access P) (F : Family) (h : Metadata F) : prepare P F ∈ FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a F h) _ _ _ _ (h.coordinate.comp (IntegralMixedVirtualTaskBits.saved_FP P a))

theorem prepare_root (P : Parameters) (F : Family) (q : List Bool) : RankedHistoryTask.root (prepare P F q) = RankedHistoryTask.root q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_root, id_eq]
theorem prepare_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (prepare P F q) = birth P q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_birth, id_eq]
theorem prepare_phase (P : Parameters) (F : Family) (q : List Bool) : phase (prepare P F q) = 26 :=
  IntegralMixedValueFieldQuery.query_phase P _ _ _ _ _ q
theorem prepare_routine (P : Parameters) (F : Family) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (prepare P F q) = 4 :=
  IntegralMixedValueFieldQuery.query_routine P _ _ _ _ _ q

theorem prepare_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (prepare P F q) = IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P id _ _ _ _ q (by decide))
theorem prepare_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (prepare P F q) = modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P _ _ _ _ _ q (by decide)).trans
    (IntegralMixedValueFieldQuery.query_modulus P id _ _ _ _ q (by decide))

theorem prepare_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (f : Field) :
    get P f (prepare P F q) = if f = .slot14 then 4 else
      if f = .slot13 then coordinate F (IntegralMixedVirtualTaskBits.saved P q) else
      if f = .slot8 then choice F (IntegralMixedVirtualTaskBits.saved P q) else get P f q := by
  simp only [prepare, first, IntegralMixedValueFieldQuery.query_get, IntegralMixedValueFieldQuery.query_root, id_eq]
  rw [min_eq_left (coordinate_cap P F g q), min_eq_left (choice_cap P F g q)]
  cases f <;> rfl

theorem prepare_coordinate_kind (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (ht : tag F (IntegralMixedVirtualTaskBits.saved P q) = 2) :
    F.kind (IntegralMixedVirtualTaskBits.saved P (prepare P F q)) =
      IntegralMixedCoordinateCoefficientSnapshot.kind F (IntegralMixedVirtualTaskBits.saved P (prepare P F q))
        (get P .slot13 (prepare P F q)) (get P .slot8 (prepare P F q)) := by
  rw [prepare_saved]
  simp only [prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact coordinate_kind F _ ht

theorem raw_value_prepare (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedNormalizationTopBits.rawCutValue P F (prepare P F q) = IntegralMixedNormalizationTopBits.rawCutValue P F q := by
  unfold IntegralMixedNormalizationTopBits.rawCutValue
  rw [prepare_saved, prepare_modulus]
  simp only [prepare_get P F g q, reduceCtorEq, ite_false]

end LeanCanny.Algebra.IntegralMixedRawKindBits

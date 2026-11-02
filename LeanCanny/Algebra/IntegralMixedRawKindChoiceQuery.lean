/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
/-! # Native lower-choice packets retain the actual parent and coordinate

This changes a local finite choice query, never a creating command or an
old prefix. The request is clipped at the original creating choice; native
validity tests separately guard labels against that bound.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindChoiceBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def requested (P : Parameters) : List Bool→ℕ := get P .slot8
noncomputable def selected (P : Parameters) (F : Family) (q : List Bool) :=
  min (requested P q) (IntegralMixedRawKindBits.choice F (IntegralMixedVirtualTaskBits.saved P q))
theorem selected_binary (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedRawKindBits.Metadata F) :
    BinaryFn (selected P F) := by
  have HL:=get_binary P a .slot8
  have HR:=h.choice.comp (IntegralMixedVirtualTaskBits.saved_FP P a)
  exact (BinaryFn.ite (HL.le HR) HL HR).of_eq (fun q=>Nat.min_def.symm)

noncomputable def query (P : Parameters) (F : Family) :=
  IntegralMixedValueFieldQuery.query P (IntegralMixedRawKindBits.prepare P F) .rawFactor .companion .slot8 (selected P F)
theorem query_FP (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedRawKindBits.Metadata F) : query P F∈FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (IntegralMixedRawKindBits.prepare_FP P a F h) _ _ _ _ (selected_binary P a F h)

theorem query_root (P : Parameters) (F : Family) (q : List Bool) : RankedHistoryTask.root (query P F q)=RankedHistoryTask.root q :=
  (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ q).trans (IntegralMixedRawKindBits.prepare_root P F q)
theorem query_birth (P : Parameters) (F : Family) (q : List Bool) : birth P (query P F q)=birth P q :=
  (IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ q).trans (IntegralMixedRawKindBits.prepare_birth P F q)
theorem query_phase (P : Parameters) (F : Family) (q : List Bool) : isPhase .companion (query P F q) :=
  IntegralMixedValueFieldQuery.query_phase P _ _ _ _ _ q
theorem query_routine (P : Parameters) (F : Family) (q : List Bool) : IntegralMixedRoutineTaskBits.routine P (query P F q)=4 :=
  IntegralMixedValueFieldQuery.query_routine P _ _ _ _ _ q
theorem query_saved (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P F q)=IntegralMixedVirtualTaskBits.saved P q :=
  (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ q (by decide)).trans (IntegralMixedRawKindBits.prepare_saved P F q)
theorem query_modulus (P : Parameters) (F : Family) (q : List Bool) : modulus P (query P F q)=modulus P q :=
  (IntegralMixedValueFieldQuery.query_modulus P _ _ _ _ _ q (by decide)).trans (IntegralMixedRawKindBits.prepare_modulus P F q)

attribute [local irreducible] IntegralMixedRawKindBits.prepare

theorem query_get (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) (f : Field) :
    get P f (query P F q)=if f=.slot14 then 4 else if f=.slot8 then selected P F q else
      if f=.slot13 then IntegralMixedRawKindBits.coordinate F (IntegralMixedVirtualTaskBits.saved P q) else get P f q := by
  rw [query,IntegralMixedValueFieldQuery.query_get]
  have HB : selected P F q≤numericCap P (RankedHistoryTask.root (IntegralMixedRawKindBits.prepare P F q)) := by
    rw [IntegralMixedRawKindBits.prepare_root]
    exact (min_le_right _ _).trans (IntegralMixedRawKindBits.choice_cap P F g q)
  rw [min_eq_left HB,IntegralMixedRawKindBits.prepare_get P F g q]
  cases f <;> simp only [reduceCtorEq,ite_false,ite_true,IntegralMixedRoutineTaskBits.Routine.code]

theorem query_valid (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedVirtualCaps.valid P (query P F q)↔IntegralMixedVirtualCaps.valid P q := by
  unfold IntegralMixedVirtualCaps.valid
  rw [query_birth,query_root]
theorem query_context (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    IntegralMixedVirtualContextBits.context P (query P F q)↔IntegralMixedVirtualContextBits.context P q := by
  unfold IntegralMixedVirtualContextBits.context
  simp only [query_get P F g q,reduceCtorEq,ite_false]

end LeanCanny.Algebra.IntegralMixedRawKindChoiceBits

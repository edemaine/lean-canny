/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedValueFieldQuery
/-! # Indexed coefficient/choice requests preserve the selected parent

The context is (original parent task, (coefficient, finite choice)). Both
indices remain binary. Only local fields3/8 are replaced; the source root,
old prefix, selected context and original scalar modulus remain literal.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask

def coefficient (z : List Bool) := Nat.fromBitsLE (pairFst (pairSnd z))
def choice (z : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd z))
theorem coefficient_binary : BinaryFn coefficient := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem choice_binary : BinaryFn choice := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

def first (P : Parameters) := IntegralMixedValueFieldQuery.query P pairFst .rawFactor .companion .coefficient coefficient
def query (P : Parameters) := IntegralMixedValueFieldQuery.query P (first P) .rawFactor .companion .slot8 choice
theorem first_FP (P : Parameters) (a : Access P) : first P∈FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ pairFst_mem_FP _ _ _ _ coefficient_binary
theorem query_FP (P : Parameters) (a : Access P) : query P∈FP :=
  IntegralMixedValueFieldQuery.query_FP P a _ (first_FP P a) _ _ _ _ choice_binary

theorem query_saved (P : Parameters) (z : List Bool) :
    IntegralMixedVirtualTaskBits.saved P (query P z)=IntegralMixedVirtualTaskBits.saved P (pairFst z) :=
  (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ z (by decide)).trans
    (IntegralMixedValueFieldQuery.query_saved P _ _ _ _ _ z (by decide))
theorem query_root (P : Parameters) (z : List Bool) : RankedHistoryTask.root (query P z)=RankedHistoryTask.root (pairFst z) :=
  (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ z).trans (IntegralMixedValueFieldQuery.query_root P _ _ _ _ _ z)
theorem query_birth (P : Parameters) (z : List Bool) : birth P (query P z)=birth P (pairFst z) :=
  (IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ z).trans (IntegralMixedValueFieldQuery.query_birth P _ _ _ _ _ z)

theorem query_get (P : Parameters) (z : List Bool) (f : Field) :
    get P f (query P z)=if f=.slot14 then 4 else if f=.slot8 then min (choice z) (numericCap P (RankedHistoryTask.root (pairFst z))) else
      if f=.coefficient then min (coefficient z) (numericCap P (RankedHistoryTask.root (pairFst z))) else get P f (pairFst z) := by
  simp only [query,first,IntegralMixedValueFieldQuery.query_get,IntegralMixedValueFieldQuery.query_root]
  cases f <;> simp only [reduceCtorEq,ite_true,ite_false,IntegralMixedRoutineTaskBits.Routine.code]

end LeanCanny.Algebra.IntegralMixedCutCoefficientQueryBits

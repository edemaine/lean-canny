/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindRetarget
/-! # The same immutable raw packet restores actual value-cut choices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem value_kind (F : Family) (key : List Bool) (ht : tag F key = 4) :
    F.kind key = IntegralMixedValueCoefficientSnapshot.kind F key (coordinate F key) (choice F key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c =>
    simp only [coordinate, choice, hk, IntegralMixedValueCoefficientSnapshot.kind]
    congr 1
    · apply Fin.ext
      exact (Nat.mod_eq_of_lt j.isLt).symm
    · apply Fin.ext
      exact (Nat.mod_eq_of_lt c.isLt).symm

theorem prepare_value_kind (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (ht : tag F (IntegralMixedVirtualTaskBits.saved P q) = 4) :
    F.kind (IntegralMixedVirtualTaskBits.saved P (prepare P F q)) =
      IntegralMixedValueCoefficientSnapshot.kind F (IntegralMixedVirtualTaskBits.saved P (prepare P F q))
        (get P .slot13 (prepare P F q)) (get P .slot8 (prepare P F q)) := by
  rw [prepare_saved]
  simp only [prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact value_kind F _ ht

end LeanCanny.Algebra.IntegralMixedRawKindBits

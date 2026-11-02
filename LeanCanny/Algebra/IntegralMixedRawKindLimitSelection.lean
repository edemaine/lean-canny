/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindSquarefreeSelection
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateSnapshot

/-! # Raw tag five restores the immutable limit-coordinate payload -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical

noncomputable def limitKind (F : Family) (key : List Bool) (j c : ℕ) :
    IntegralMixedRelativeCuts.Kind (F.spatial key) (F.rule key) :=
  .limitCoordinate (IntegralMixedLimitCoordinateSnapshot.coordinate F key j)
    (IntegralMixedLimitCoordinateSnapshot.choice F key c)

theorem limit_kind (F : Family) (key : List Bool) (ht : tag F key = 5) :
    F.kind key = limitKind F key (coordinate F key) (choice F key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c => simp only [tag, hk] at ht; omega
  | limitCoordinate j c =>
    simp only [coordinate, choice, hk, limitKind,
      IntegralMixedLimitCoordinateSnapshot.coordinate_fin, IntegralMixedLimitCoordinateSnapshot.choice_fin]

theorem limit_choice_lt (F : Family) (key : List Bool) (ht : tag F key = 5) :
    choice F key < IntegralMixedLimitCoordinate.ChoiceBound (F.spatial key) (F.rule key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c => simp only [tag, hk] at ht; omega
  | limitCoordinate j c => simpa only [choice, hk] using c.isLt

theorem prepare_limit_kind (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (ht : tag F (IntegralMixedVirtualTaskBits.saved P q) = 5) :
    F.kind (IntegralMixedVirtualTaskBits.saved P (prepare P F q)) =
      limitKind F (IntegralMixedVirtualTaskBits.saved P (prepare P F q))
        (get P .slot13 (prepare P F q)) (get P .slot8 (prepare P F q)) := by
  rw [prepare_saved]
  simp only [prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact limit_kind F _ ht

theorem limit_factor (F : Family) (key : List Bool) (ht : tag F key = 5) :
    IntegralMixedRelativeCuts.factor (F.state key) (F.birth_bound key) (F.rule key) (F.kind key) =
      IntegralMixedLimitCoordinateSnapshot.factor F key (coordinate F key) (choice F key) := by
  rw [limit_kind F key ht]
  rfl

end LeanCanny.Algebra.IntegralMixedRawKindBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRawKindPreparedFields
public import LeanCanny.Algebra.IntegralMixedPscEntrySnapshot
/-! # Immutable squarefree choices agree with the actual PSC source indices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def squarefreeKind (F : Family) (key : List Bool) (j c : ℕ) : IntegralMixedRelativeCuts.Kind (F.spatial key) (F.rule key) :=
  .squarefree ((IntegralMixedPscEntrySnapshot.indices F j).coordinate key)
    (IntegralMixedPscEntrySnapshot.index F c key)

theorem squarefree_kind (F : Family) (key : List Bool) (ht : tag F key = 3) :
    F.kind key = squarefreeKind F key (coordinate F key) (choice F key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c =>
    simp only [coordinate, choice, hk, squarefreeKind,
      IntegralMixedPscEntrySnapshot.indices, IntegralMixedPscEntrySnapshot.index,
      Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt c.isLt]
  | value j c => simp only [tag, hk] at ht; omega

theorem squarefree_choice_lt (F : Family) (key : List Bool) (ht : tag F key = 3) :
    choice F key < IntegralMixedCoordinateSquarefree.coordinateDegree (F.spatial key) (F.rule key) := by
  cases hk : F.kind key with
  | coordinate j c => simp only [tag, hk] at ht; omega
  | squarefree j c => simpa only [choice, hk] using c.isLt
  | value j c => simp only [tag, hk] at ht; omega

theorem prepare_squarefree_kind (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (q : List Bool) (ht : tag F (IntegralMixedVirtualTaskBits.saved P q) = 3) :
    F.kind (IntegralMixedVirtualTaskBits.saved P (prepare P F q)) =
      squarefreeKind F (IntegralMixedVirtualTaskBits.saved P (prepare P F q))
        (get P .slot13 (prepare P F q)) (get P .slot8 (prepare P F q)) := by
  rw [prepare_saved]
  simp only [prepare_get P F g q, reduceCtorEq, ite_false, ite_true]
  exact squarefree_kind F _ ht

end LeanCanny.Algebra.IntegralMixedRawKindBits

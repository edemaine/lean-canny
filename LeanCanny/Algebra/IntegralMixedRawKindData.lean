/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCoordinateCoefficientSource
public import LeanCanny.Algebra.IntegralMixedValueCoefficientSource
/-! # Immutable raw-cut tags and finite original choice payloads -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawKindBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedExceptionalBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def tag (F : Family) (key : List Bool) : ℕ := match F.kind key with
  | .coordinate .. => 2 | .squarefree .. => 3 | .value .. => 4
noncomputable def coordinate (F : Family) (key : List Bool) : ℕ := match F.kind key with
  | .coordinate j _ => j.val | .squarefree j _ => j.val | .value j _ => j.val
noncomputable def choice (F : Family) (key : List Bool) : ℕ := match F.kind key with
  | .coordinate _ c => c.val | .squarefree _ c => c.val | .value _ c => c.val

structure Metadata (F : Family) : Prop where
  tag : BinaryFn (tag F)
  coordinate : BinaryFn (coordinate F)
  choice : BinaryFn (choice F)

theorem tag_bounds (F : Family) (key : List Bool) : 2 ≤ tag F key ∧ tag F key ≤ 4 := by
  cases hk : F.kind key <;> simp only [tag, hk] <;> omega

theorem coordinate_le (F : Family) (key : List Bool) : coordinate F key ≤ F.ambient key := by
  cases hk : F.kind key with
  | coordinate j c => have hj := j.isLt; simpa only [coordinate, hk] using (by omega : j.val ≤ F.ambient key)
  | squarefree j c => have hj := j.isLt; simpa only [coordinate, hk] using (by omega : j.val ≤ F.ambient key)
  | value j c => have hj := j.isLt; simpa only [coordinate, hk] using (by omega : j.val ≤ F.ambient key)

theorem choice_le (F : Family) (key : List Bool) : choice F key ≤ auxiliaryCap (F.ambient key + 1) (F.spatial key).degree := by
  cases hk : F.kind key with
  | coordinate j c =>
    have hc := c.isLt
    have hb := coordinateCap_le (F.spatial key).degree (F.rule key)
    change c.val < PurePowerReductionBounds.dimension (F.ambient key - (F.rule key).critical.offset.val + 1) (F.spatial key).degree + 1 at hc
    simp only [choice, hk]
    unfold auxiliaryCap
    omega
  | squarefree j c =>
    have hc := c.isLt
    have hb := coordinateCap_le (F.spatial key).degree (F.rule key)
    change c.val < PurePowerReductionBounds.dimension (F.ambient key - (F.rule key).critical.offset.val + 1) (F.spatial key).degree at hc
    simp only [choice, hk]
    unfold auxiliaryCap
    omega
  | value j c =>
    have hc := c.isLt
    have hb := value_dimension_le (F.spatial key) (F.rule key)
    have hd := (F.spatial key).degree_two
    have hv : valueDimension (F.ambient key + 1) (F.spatial key).degree ≤ valueCap (F.ambient key + 1) (F.spatial key).degree := by
      unfold valueCap
      exact Nat.le_mul_of_pos_right _ (by omega)
    change c.val < IntegralMixedGridValue.dimension (F.spatial key) (F.rule key) + 2 at hc
    simp only [choice, hk]
    unfold auxiliaryCap
    omega

theorem coordinate_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    coordinate F (IntegralMixedVirtualTaskBits.saved P q) ≤ numericCap P (RankedHistoryTask.root q) :=
  (coordinate_le F _).trans ((g.ambient q).trans ((Nat.le_succ _).trans
    (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.1))

theorem choice_cap (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    choice F (IntegralMixedVirtualTaskBits.saved P q) ≤ numericCap P (RankedHistoryTask.root q) := by
  have hc := (choice_le F (IntegralMixedVirtualTaskBits.saved P q)).trans (F.scalar_cap _)
  rw [g.width q] at hc
  exact hc.trans (IntegralCriticalQueryBounds.metadata_le _ _ _ _ _ _ _ _).2.2.2.2.2.1

theorem coordinate_kind (F : Family) (key : List Bool) (ht : tag F key = 2) :
    F.kind key = IntegralMixedCoordinateCoefficientSnapshot.kind F key (coordinate F key) (choice F key) := by
  cases hk : F.kind key with
  | coordinate j c =>
    simp only [coordinate, choice, hk, IntegralMixedCoordinateCoefficientSnapshot.kind,
      IntegralMixedCoordinateCoefficientSnapshot.coordinate, IntegralMixedCoordinateCoefficientSnapshot.choice,
      Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt c.isLt]
  | squarefree j c => simp only [tag, hk] at ht; omega
  | value j c => simp only [tag, hk] at ht; omega

end LeanCanny.Algebra.IntegralMixedRawKindBits

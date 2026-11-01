/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullHeightNaturalBridge
/-! # Actual physical and virtual scalar heights vanish beyond the spatial coordinates -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullHeightNaturalBridge
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical_invalid (P : Parameters) (F : IntegralMixedPhysicalCriticalBits.Family) (q : List Bool)
    (hi : ¬get P .slot8 q < F.ambient (IntegralMixedPhysicalTaskBits.saved P q) + 1) :
    IntegralMixedPhysicalNativeLowerBits.height P F q = [] := by
  let _ := (IntegralMixedPhysicalNativeLowerBits.source P F).ring q
  rw [IntegralMixedPhysicalNativeLowerBits.height_eq]
  have he : (IntegralMixedPhysicalNativeLowerBits.source P F).height q (get P .slot8 q) = 0 := by
    change CoordinateFrozenCriticalElimination.numerators
      (IntegralMixedHistory.data (F.state (IntegralMixedPhysicalTaskBits.saved P q))
        (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (F.rule (IntegralMixedPhysicalTaskBits.saved P q))).scales
      (IntegralMixedHistory.data (F.state (IntegralMixedPhysicalTaskBits.saved P q))
        (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (F.rule (IntegralMixedPhysicalTaskBits.saved P q))).heights
      (get P .slot8 q) = 0
    rw [CoordinateFrozenCriticalElimination.numerators, dite_eq_right hi]
  rw [he, map_zero, Matrix.zero_apply, Int.cast_zero]
  exact (ArithmeticBits.zero_residueBits _).symm

theorem virtual_invalid (P : Parameters) (F : IntegralMixedCutSource.Family) (q : List Bool)
    (hi : ¬get P .slot8 q < F.ambient (IntegralMixedVirtualTaskBits.saved P q) + 1) :
    IntegralMixedVirtualNativeLowerBits.height P F q = [] := by
  let _ := (IntegralMixedVirtualNativeLowerBits.source P F).ring q
  rw [IntegralMixedVirtualNativeLowerBits.height_eq]
  have he : (IntegralMixedVirtualNativeLowerBits.source P F).height q (get P .slot8 q) = 0 := by
    change AdjoinRoot.mk (Polynomial.X ^ (2 ^ F.width (IntegralMixedVirtualTaskBits.saved P q)))
      (CoordinateFrozenCriticalElimination.numerators
        (IntegralMixedHistory.data (F.state (IntegralMixedVirtualTaskBits.saved P q))
          (F.birth_bound (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q)).critical).scales
        (IntegralMixedCriticalSweep.heights (F.state (IntegralMixedVirtualTaskBits.saved P q))
          (F.rule (IntegralMixedVirtualTaskBits.saved P q))) (get P .slot8 q)) = 0
    rw [CoordinateFrozenCriticalElimination.numerators, dite_eq_right hi, map_zero]
  rw [he, map_zero, Matrix.zero_apply, Int.cast_zero]
  exact (ArithmeticBits.zero_residueBits _).symm

end LeanCanny.Algebra.IntegralMixedFullHeightNaturalBridge

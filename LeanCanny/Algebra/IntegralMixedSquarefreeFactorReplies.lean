/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorValue
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorTasks
public import LeanCanny.Algebra.IntegralMixedPscEntrySnapshot
/-! # Literal lower replies for the squarefree scalar product -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.matrix

noncomputable def determinantEntry (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry
    (Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state key)).finBasis
      (IntegralMixedSquarefreeMatrixSource.matrix (F.state key) (F.birth_bound key) (F.rule key)
        ((IntegralMixedPscEntrySnapshot.indices F j).coordinate key) (IntegralMixedPscEntrySnapshot.index F c key)).det) r t

theorem determinant_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry
      ((IntegralMixedPscUpperBits.characteristic P F).coefficientMatrix q 0) r t =
      determinantEntry F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) r t := by
  change IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedPscCharacteristicBits.source P F).coefficientMatrix q 0) r t = _
  rw [IntegralMixedPscCharacteristicBits.coefficient_zero]
  rfl

theorem top_value (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F) (q : List Bool) :
    (IntegralMixedVirtualTaskBits.source P F).value (IntegralMixedSquarefreeFactorTasks.top P F q) =
      residueBits (integer P F q : ZMod (modulus P q)) := by
  rw [IntegralMixedVirtualTaskBits.value_snapshot, IntegralMixedSquarefreeFactorTasks.top_saved,
    IntegralMixedSquarefreeFactorTasks.top_modulus]
  simp only [IntegralMixedVirtualTaskBits.coordinate, IntegralMixedSquarefreeFactorTasks.top_get P F g,
    reduceCtorEq, ite_false, ite_true, or_true, or_false]
  change residueBits ((IntegralMixedVirtualQueryBits.matrixCoefficient F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (IntegralMixedCoordinateSquarefree.coordinateDegree
      (F.spatial (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q))) 0 0 : ℤ) :
        ZMod (modulus P q)) = _
  rw [coordinate_top]
  rfl

theorem determinant_value (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPscUpperBits.characteristicValue P F (IntegralMixedSquarefreeFactorTasks.determinant P q) =
      IntegralMixedPscUpperBits.characteristicValue P F q := by
  unfold IntegralMixedPscUpperBits.characteristicValue
  rw [determinant_snapshot, determinant_snapshot, IntegralMixedSquarefreeFactorTasks.determinant_saved,
    IntegralMixedSquarefreeFactorTasks.determinant_modulus]
  simp only [IntegralMixedSquarefreeFactorTasks.determinant_get, reduceCtorEq, ite_false]

end LeanCanny.Algebra.IntegralMixedSquarefreeFactorBits

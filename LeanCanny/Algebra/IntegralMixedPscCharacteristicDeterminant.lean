/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscCharacteristicSource
/-! # The constant negative-PSC characteristic coefficient is the determinant -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscCharacteristicBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.matrix

theorem coefficient_zero (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).coefficientMatrix q 0 = Algebra.leftMulMatrix
      (IntegralMixedCutNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q)).finBasis
      ((IntegralMixedSquarefreeMatrixSource.matrix ((IntegralMixedVirtualTaskBits.family P F).state q)
        ((IntegralMixedVirtualTaskBits.family P F).birth_bound q) ((IntegralMixedVirtualTaskBits.family P F).rule q)
        ((IntegralMixedVirtualTaskBits.indices P F).coordinate q) (IntegralMixedPscEntryBits.index P F q)).det) := by
  let := (IntegralMixedPscEntryBits.source P F).ring q
  let read := Algebra.leftMulMatrix ((IntegralMixedPscEntryBits.source P F).basis q)
  have H := congrArg read (IntegralMixedValueDeterminantSource.negative_charpoly_constant
    ((IntegralMixedPscEntryBits.source P F).matrix q))
  exact H

end LeanCanny.Algebra.IntegralMixedPscCharacteristicBits

/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableArithmetic
public import LeanCanny.Algebra.IntegralMixedAffineMatrix
/-! # The un-erased affine postprocessor is the actual height matrix entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedOldHeightBits (state bankFamily)
open IntegralMixedFramedHeightTableMatrixBits (row col)
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedFramedScalarCellsBits.affine

theorem affine_matrix (P : Parameters) (D : Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (q : List Bool) :
    IntegralMixedFramedHeightIntegerBits.affine P D J q=
      Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
        (IntegralMixedHistory.expression (state P D J q) (IntegralMixedFramedScalarCellsBits.affine P D J q))
        (row P D J q) (col P D J q) := by
  have HS : IntegralMixedFramedHeightIntegerBits.references P D J q=
      ∑i : Fin ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q)),
        IntegralMixedAffineCoefficients.referenceCoefficient (IntegralMixedFramedScalarCellsBits.affine P D J q) i.val*
          Algebra.leftMulMatrix (state P D J q).sampler.scalarPrefix.basis.finBasis
            (IntegralMixedHistory.cleared (state P D J q) i) (row P D J q) (col P D J q) := by
    unfold IntegralMixedFramedHeightIntegerBits.references
    rw [←IntegralMixedFramedOldHeightBits.bank_birth P D J q,←Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [IntegralMixedFramedHeightTableMatrixBits.matrix_entry P D J q i]
    rfl
  have HD : row P D J q=col P D J q ↔
      IntegralMixedHeightTableQueryBits.oldRow P q=IntegralMixedHeightTableQueryBits.oldCol P q := Fin.ext_iff
  rw [IntegralMixedAffineMatrix.entry,IntegralMixedFramedHeightIntegerBits.affine,HS]
  unfold IntegralMixedFramedHeightIntegerBits.bank IntegralMixedFramedHeightIntegerBits.constant
  by_cases he : row P D J q=col P D J q
  · rw [ite_eq_left he,ite_eq_left (HD.mp he)]
    rw [show IntegralMixedFramedScalarCellsBits.cell P D J q 0 0=
      IntegralMixedAffineCoefficients.constantCoefficient (IntegralMixedFramedScalarCellsBits.affine P D J q) from rfl]
    ring
  · rw [ite_eq_right he,ite_eq_right (fun h=>he (HD.mpr h))]
    ring

end LeanCanny.Algebra.IntegralMixedFramedPhysicalAffineBits

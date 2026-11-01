/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueTaskBounds

/-! # The guarded homogeneous coordinate child is the actual row coefficient

The child is an ordinary virtual critical coefficient query of the same
selected parent. This identifies its actual model with the coordinate
polynomial used by the double-nilpotent Gram system; no new coefficient
oracle is introduced.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueCoordinateChild
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedValueHomogeneousQueries IntegralMixedVirtualCaps
open scoped Classical

theorem matrixCoefficient_eq (F : Family) (q : List Bool) (j k r t : ℕ) :
    IntegralMixedVirtualQueryBits.matrixCoefficient F q j k r t =
      Algebra.leftMulMatrix (IntegralMixedCutNilpotent.basis (F.state q)).finBasis
        ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state q) (F.birth_bound q) (F.rule q)
          ⟨j % (F.ambient q - (F.rule q).critical.offset.val + 1), Nat.mod_lt _ (by omega)⟩).coeff k)
        ⟨r % count (F.birth q + 1) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
        ⟨t % count (F.birth q + 1) (F.width q), Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩ := by
  rw [IntegralMixedSquarefreeMatrixSource.coordinateImage, Polynomial.coeff_map]
  rfl

theorem value (P : Parameters) (F : Family) (h : RootGeometry P F) (q : List Bool)
    (hr : HomogeneousSystemCoefficientRequest.request (parameters P F) (packet P q))
    (hz : get P .slot8 q ≠ 0) :
    (IntegralMixedVirtualTaskBits.source P F).value (coordinateTask P F q) =
      residueBits ((Algebra.leftMulMatrix
        (IntegralMixedCutNilpotent.basis (F.state (IntegralMixedVirtualTaskBits.saved P q))).finBasis
        ((IntegralMixedSquarefreeMatrixSource.coordinateImage (F.state (IntegralMixedVirtualTaskBits.saved P q))
          (F.birth_bound (IntegralMixedVirtualTaskBits.saved P q)) (F.rule (IntegralMixedVirtualTaskBits.saved P q))
          ⟨(get P .slot8 q - 1) % (F.ambient (IntegralMixedVirtualTaskBits.saved P q) -
            (F.rule (IntegralMixedVirtualTaskBits.saved P q)).critical.offset.val + 1), Nat.mod_lt _ (by omega)⟩).coeff
              (IntegralMixedValueHomogeneousQueries.coordinateCoefficient P F q))
          ((IntegralMixedVirtualTaskBits.indices P F).row q) ((IntegralMixedVirtualTaskBits.indices P F).col q) : ℤ) :
            ZMod (modulus P q)) := by
  rw [IntegralMixedValueTaskBounds.coordinateTask_value_guarded P F h q hr hz, matrixCoefficient_eq]
  rfl

end LeanCanny.Algebra.IntegralMixedValueCoordinateChild
